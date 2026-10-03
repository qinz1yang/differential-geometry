import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.Path.Composition
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem contMDiffOn_lift {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f)
    {γ : ℝ → N} {η : ℝ → M} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) J 1 γ s) (hη : ContinuousOn η s)
    (hlift : EqOn (f ∘ η) γ s) : ContMDiffOn 𝓘(ℝ) I 1 η s := by
  intro t ht
  obtain ⟨φ, hsource, heq⟩ := hf (η t)
  have htarget : γ t ∈ φ.target := by
    rw [← hlift ht, Function.comp_apply, heq hsource]
    exact φ.map_source hsource
  have hbranch : ContMDiffWithinAt 𝓘(ℝ) I 1 (φ.symm ∘ γ) s t :=
    ((φ.contMDiffOn_invFun.contMDiffAt (φ.open_target.mem_nhds htarget)).of_le
      (by norm_num)).comp_contMDiffWithinAt t (hγ t ht)
  have hlocal : η =ᶠ[𝓝[s] t] φ.symm ∘ γ := by
    filter_upwards [(hη t ht).preimage_mem_nhdsWithin (φ.open_source.mem_nhds hsource),
      self_mem_nhdsWithin] with r hr hs
    change η r = φ.symm (γ r)
    rw [← hlift hs, Function.comp_apply, heq hr]
    exact (φ.left_inv hr).symm
  exact hbranch.congr_of_eventuallyEq hlocal (hlocal.eq_of_nhdsWithin ht)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem riemannianEDistOf_lift_le_pathELength
    [IsManifold I ∞ M] [IsManifold J ∞ N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    {a b : ℝ} (hab : a ≤ b) {γ : ℝ → N} {η : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ) J 1 γ (Icc a b)) (hη : ContinuousOn η (Icc a b))
    (hlift : EqOn (f ∘ η) γ (Icc a b)) :
    let : RiemannianBundle (fun x : N => TangentSpace J x) := ⟨h.toRiemannianMetric⟩
    riemannianEDistOf g (η a) (η b) ≤ pathELength J γ a b := by
  let : RiemannianBundle (fun x : N => TangentSpace J x) := ⟨h.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hsmooth := contMDiffOn_lift hf hγ hη hlift
  have hlength : pathELength I η a b = pathELength J (f ∘ η) a b := by
    apply (Manifold.pathELength_comp_eq_of_enorm_mfderiv_eq f ?_ ?_ ?_).symm
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact ((hsmooth.mdifferentiableOn one_ne_zero) t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
        (Icc_mem_nhds ht.1 ht.2)
    · exact Eventually.of_forall fun t => hf.contMDiff.mdifferentiableAt (by norm_num)
    · apply Eventually.of_forall
      intro t
      rw [← ofReal_norm, ← ofReal_norm, norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
      change ENNReal.ofReal (Real.sqrt (h.inner (f (η t))
          (mfderiv I J f (η t) (mfderiv 𝓘(ℝ) I η t 1))
          (mfderiv I J f (η t) (mfderiv 𝓘(ℝ) I η t 1)))) =
        ENNReal.ofReal (Real.sqrt (g.inner (η t) (mfderiv 𝓘(ℝ) I η t 1)
          (mfderiv 𝓘(ℝ) I η t 1)))
      rw [hmetric]
  change riemannianEDist I (η a) (η b) ≤ _
  exact (riemannianEDist_le_pathELength hsmooth rfl rfl hab).trans_eq
    (hlength.trans (pathELength_congr hlift))

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_pathELength_bound
    [IsManifold J ∞ N]
    [RiemannianBundle (fun x : N => TangentSpace J x)]
    [IsContinuousRiemannianBundle F (fun x : N => TangentSpace J x)]
    {γ : ℝ → N} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ) J 1 γ (Icc a b)) :
    ∃ K : ℝ≥0, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      pathELength J γ s t ≤ K * ENNReal.ofReal (t - s) := by
  have hinput : Continuous (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hvel : ContinuousOn
      (fun t => (⟨γ t, mfderivWithin 𝓘(ℝ) J γ (Icc a b) t 1⟩ : TangentBundle J N))
      (Icc a b) := by
    exact (hγ.continuousOn_tangentMapWithin (by norm_num)
      (uniqueDiffOn_Icc hab).uniqueMDiffOn).comp hinput.continuousOn (fun t ht => ht)
  have hspeed : ContinuousOn (fun t => ‖mfderivWithin 𝓘(ℝ) J γ (Icc a b) t 1‖) (Icc a b) := by
    simpa only [norm_eq_sqrt_real_inner] using (hvel.inner_bundle hvel).sqrt
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hspeed
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  refine ⟨K, ?_⟩
  intro s hs t ht
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  calc
    (∫⁻ r in Ioo s t, ‖mfderiv 𝓘(ℝ) J γ r 1‖ₑ) ≤ ∫⁻ _r in Ioo s t, (K : ℝ≥0∞) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      have hrab : r ∈ Ioo a b := ⟨hs.1.trans_lt hr.1, hr.2.trans_le ht.2⟩
      have hn : ‖mfderivWithin 𝓘(ℝ) J γ (Icc a b) r 1‖ ≤ K :=
        (hC ⟨r, ⟨hrab.1.le, hrab.2.le⟩, rfl⟩).trans (le_max_left _ _)
      rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds hrab.1 hrab.2)] at hn
      rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hn
    _ = K * ENNReal.ofReal (t - s) := by rw [lintegral_const, Measure.restrict_apply_univ,
      Real.volume_Ioo]

variable [FiniteDimensional ℝ E]
  [IsManifold I ∞ M] [IsManifold J ∞ N]
  [T2Space M] [SigmaCompactSpace M] [T2Space N]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_tendsto_lift_of_complete
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f)
    (hg : RiemannianMetricComplete (I := I) g)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    {a b : ℝ} (hab : a < b)
    {γ : ℝ → N} (hγ : ContMDiffOn 𝓘(ℝ) J 1 γ (Icc a b))
    {η : ℝ → M} (hη : ContinuousOn η (Ico a b))
    (hlift : EqOn (f ∘ η) γ (Ico a b)) :
    ∃ x : M, Tendsto η (𝓝[<] b) (𝓝 x) ∧ f x = γ b := by
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by norm_num)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hg.complete
  let : RiemannianBundle (fun x : N => TangentSpace J x) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F (fun x : N => TangentSpace J x) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  obtain ⟨K, hK⟩ := exists_pathELength_bound hab hγ
  have hordered (s : ℝ) (hs : s ∈ Ico a b) (t : ℝ) (ht : t ∈ Ico a b) (hst : s ≤ t) :
      edist (η s) (η t) ≤ K * edist s t := by
    have hsub : Icc s t ⊆ Ico a b := fun r hr => ⟨hs.1.trans hr.1, hr.2.trans_lt ht.2⟩
    have hdist := riemannianEDistOf_lift_le_pathELength g h hf hmetric hst
      (hγ.mono (fun r hr => ⟨hs.1.trans hr.1, hr.2.trans ht.2.le⟩))
      (hη.mono hsub) (hlift.mono hsub)
    change edist (η s) (η t) ≤ _ at hdist
    have hlen := hK s ⟨hs.1, hs.2.le⟩ t ⟨ht.1, ht.2.le⟩
    rw [edist_dist s t, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)]
    simpa only [neg_sub] using hdist.trans hlen
  have hlip : LipschitzOnWith K η (Ico a b) := by
    intro s hs t ht
    rcases le_total s t with hst | hts
    · exact hordered s hs t ht hst
    · simpa only [edist_comm] using hordered t ht s hs hts
  have htail : ∀ᶠ t in 𝓝[<] b, t ∈ Ico a b := by
    filter_upwards [(eventually_gt_nhds hab).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t hta htb
    exact ⟨hta.le, htb⟩
  have hcauchy : Cauchy (map η (𝓝[<] b)) :=
    (cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le hlip.uniformContinuousOn
      (le_principal_iff.mpr htail)
  obtain ⟨x, hx⟩ := cauchy_map_iff_exists_tendsto.mp hcauchy
  refine ⟨x, hx, ?_⟩
  have hγlim : Tendsto γ (𝓝[<] b) (𝓝 (γ b)) :=
    (hγ.continuousOn b ⟨hab.le, le_rfl⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds, htail.mono fun t ht => ⟨ht.1, ht.2.le⟩⟩)
  apply tendsto_nhds_unique (hf.contMDiff.continuous.tendsto x |>.comp hx)
  exact hγlim.congr' (htail.mono fun t ht => (hlift ht).symm)

end DifferentialGeometry.Geometry.Riemannian
