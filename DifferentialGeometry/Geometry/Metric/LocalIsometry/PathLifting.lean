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

namespace DifferentialGeometry.Geometry.Riemannian

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]

private theorem eqOn_lifts_of_initial [T2Space M]
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f)
    {γ : ℝ → N} {η ζ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hη : ContinuousOn η (Icc a b)) (hζ : ContinuousOn ζ (Icc a b))
    (hηf : EqOn (f ∘ η) γ (Icc a b)) (hζf : EqOn (f ∘ ζ) γ (Icc a b))
    (hini : η a = ζ a) : EqOn η ζ (Icc a b) := by
  let : PreconnectedSpace (Icc a b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hcomp : (fun t : Icc a b => f (η t)) = fun t : Icc a b => f (ζ t) := by
    funext t
    exact (hηf t.property).trans (hζf t.property).symm
  have heq : (fun t : Icc a b => η t) = fun t : Icc a b => ζ t :=
    (T2Space.isSeparatedMap f).eq_of_comp_eq hf.isLocalHomeomorph.isLocallyInjective
      hη.domRestrict hζ.domRestrict hcomp ⟨a, le_rfl, hab⟩ hini
  intro t ht
  exact congrFun heq ⟨t, ht⟩

private theorem exists_lift_right_extension
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f)
    {γ : ℝ → N} {a b t : ℝ} (hat : a ≤ t) (htb : t < b)
    (hγ : ContinuousOn γ (Icc a b)) {x : M} {η : ℝ → M}
    (hη : ContinuousOn η (Icc a t)) (hini : η a = x)
    (hηf : EqOn (f ∘ η) γ (Icc a t)) :
    ∃ u ∈ Ioc t b, ∃ ζ : ℝ → M,
      ContinuousOn ζ (Icc a u) ∧ ζ a = x ∧ EqOn (f ∘ ζ) γ (Icc a u) := by
  classical
  obtain ⟨φ, htφ, hφeq⟩ := hf (η t)
  have htarget : γ t ∈ φ.target := by
    rw [← hηf ⟨hat, le_rfl⟩, Function.comp_apply, hφeq htφ]
    exact φ.map_source htφ
  have hpre : γ ⁻¹' φ.target ∈ 𝓝[Icc a b] t :=
    (hγ t ⟨hat, htb.le⟩).preimage_mem_nhdsWithin (φ.open_target.mem_nhds htarget)
  obtain ⟨U, hUopen, htU, hUsub⟩ := mem_nhdsWithin.mp hpre
  obtain ⟨c, d, hcd, hcdU⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hUopen.mem_nhds htU)
  obtain ⟨u, htu, hu⟩ := exists_between (lt_min hcd.2 htb)
  have hub : u ≤ b := hu.le.trans (min_le_right _ _)
  have hmaps : MapsTo γ (Icc t u) φ.target := by
    intro s hs
    apply hUsub
    exact ⟨hcdU ⟨hcd.1.trans_le hs.1, hs.2.trans_lt (hu.trans_le (min_le_left _ _))⟩,
      hat.trans hs.1, hs.2.trans hub⟩
  let branch := φ.symm ∘ γ
  let ζ := (Iic t).piecewise η branch
  have hbranch : ContinuousOn branch (Icc t u) :=
    φ.contMDiffOn_invFun.continuousOn.comp
      (hγ.mono (Icc_subset_Icc hat hub)) hmaps
  have hjoin : η t = branch t := by
    change η t = φ.symm (γ t)
    rw [← hηf ⟨hat, le_rfl⟩, Function.comp_apply, hφeq htφ]
    exact (φ.left_inv htφ).symm
  have hζ : ContinuousOn ζ (Icc a u) := by
    apply ContinuousOn.piecewise
    · intro s hs
      have hst : s = t := Set.mem_singleton_iff.mp (frontier_Iic_subset t hs.2)
      simpa only [hst] using hjoin
    · rw [closure_Iic]
      exact hη.mono fun s hs => ⟨hs.1.1, hs.2⟩
    · rw [compl_Iic, closure_Ioi]
      exact hbranch.mono fun s hs => ⟨hs.2, hs.1.2⟩
  refine ⟨u, ⟨htu, hub⟩, ζ, hζ, ?_, ?_⟩
  · change (Iic t).piecewise η branch a = x
    rw [(Iic t).piecewise_eq_of_mem η branch hat]
    exact hini
  · intro s hs
    change f ((Iic t).piecewise η branch s) = γ s
    by_cases hst : s ≤ t
    · rw [(Iic t).piecewise_eq_of_mem η branch hst]
      exact hηf ⟨hs.1, hst⟩
    · rw [(Iic t).piecewise_eq_of_notMem η branch hst]
      have hst' : t ≤ s := (lt_of_not_ge hst).le
      have hsTarget := hmaps ⟨hst', hs.2⟩
      exact (hφeq (φ.map_target hsTarget)).trans (φ.right_inv hsTarget)

private theorem continuousOn_close_lift
    {η : ℝ → M} {a b : ℝ} (hab : a ≤ b) (hη : ContinuousOn η (Ico a b))
    {x : M} (hx : Tendsto η (𝓝[<] b) (𝓝 x)) :
    ContinuousOn (fun t => if t < b then η t else x) (Icc a b) := by
  intro t ht
  by_cases htb : t < b
  · have hmem : Ico a b ∈ 𝓝[Icc a b] t := by
      filter_upwards [(eventually_lt_nhds htb).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with s hs hsab
      exact ⟨hsab.1, hs⟩
    have hcont := (hη t ⟨ht.1, htb⟩).mono_of_mem_nhdsWithin hmem
    apply hcont.congr_of_eventuallyEq
    · filter_upwards [(eventually_lt_nhds htb).filter_mono nhdsWithin_le_nhds] with s hs
      exact ite_eq_left hs
    · exact ite_eq_left htb
  · have hteq : t = b := le_antisymm ht.2 (le_of_not_gt htb)
    subst t
    rw [← Ico_insert_right hab]
    apply ContinuousWithinAt.insert
    change Tendsto (fun t => if t < b then η t else x) (𝓝[Ico a b] b)
      (𝓝 (if b < b then η b else x))
    rw [ite_eq_right (lt_irrefl b)]
    apply (hx.mono_left (nhdsWithin_mono b Ico_subset_Iio_self)).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (ite_eq_left ht.2).symm

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold J ∞ N]
  [T2Space M] [SigmaCompactSpace M] [T2Space N]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_contMDiffOn_lift_of_complete
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f)
    (hg : RiemannianMetricComplete (I := I) g)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    {a b : ℝ} (hab : a ≤ b)
    {γ : ℝ → N} (hγ : ContMDiffOn 𝓘(ℝ) J 1 γ (Icc a b))
    (x : M) (hx : f x = γ a) :
    ∃ η : ℝ → M, ContMDiffOn 𝓘(ℝ) I 1 η (Icc a b) ∧ η a = x ∧
      EqOn (f ∘ η) γ (Icc a b) ∧
      ∀ ζ : ℝ → M, ContinuousOn ζ (Icc a b) → ζ a = x →
        EqOn (f ∘ ζ) γ (Icc a b) → EqOn ζ η (Icc a b) := by
  classical
  have hex : ∃ η : ℝ → M,
      ContinuousOn η (Icc a b) ∧ η a = x ∧ EqOn (f ∘ η) γ (Icc a b) := by
    rcases hab.eq_or_lt with rfl | hab'
    · refine ⟨fun _ => x, continuousOn_const, rfl, ?_⟩
      intro t ht
      have hta : t = a := le_antisymm ht.2 ht.1
      simpa only [Function.comp_apply, hta] using hx
    let S : Set ℝ := {t | t ∈ Icc a b ∧ ∃ η : ℝ → M,
      ContinuousOn η (Icc a t) ∧ η a = x ∧ EqOn (f ∘ η) γ (Icc a t)}
    have hconstant : EqOn (f ∘ (fun _ : ℝ => x)) γ (Icc a a) := by
      intro t ht
      have hta : t = a := le_antisymm ht.2 ht.1
      simpa only [Function.comp_apply, hta] using hx
    have haS : a ∈ S := ⟨⟨le_rfl, hab⟩, fun _ => x, continuousOn_const, rfl, hconstant⟩
    have hSne : S.Nonempty := ⟨a, haS⟩
    have hSbdd : BddAbove S := ⟨b, fun t ht => ht.1.2⟩
    let T := sSup S
    have hTle : T ≤ b := csSup_le hSne (fun t ht => ht.1.2)
    have haT : a < T := by
      obtain ⟨u, hu, η, hη, hηa, hηf⟩ := exists_lift_right_extension hf le_rfl hab'
        hγ.continuousOn (η := fun _ => x) continuousOn_const rfl hconstant
      have huS : u ∈ S := ⟨⟨hu.1.le, hu.2⟩, η, hη, hηa, hηf⟩
      exact hu.1.trans_le (le_csSup hSbdd huS)
    let lift (t : S) : ℝ → M := Classical.choose t.property.2
    have hlift (t : S) : ContinuousOn (lift t) (Icc a t.val) ∧
        lift t a = x ∧ EqOn (f ∘ lift t) γ (Icc a t.val) := Classical.choose_spec t.property.2
    have hlong : ∀ s ∈ Ico a T, ∃ t : S, s < t.val := by
      intro s hs
      obtain ⟨t, htS, hst⟩ := exists_lt_of_lt_csSup hSne hs.2
      exact ⟨⟨t, htS⟩, hst⟩
    choose pick hpick using hlong
    let η : ℝ → M := fun s => if hs : s ∈ Ico a T then lift (pick s hs) s else x
    have hagree (t : S) (s : ℝ) (hs : s ∈ Ico a T) (hst : s ≤ t.val) : η s = lift t s := by
      rw [show η s = lift (pick s hs) s by simp only [η, dite_eq_left hs]]
      have hmin : a ≤ min (pick s hs).val t.val :=
        le_min (pick s hs).property.1.1 t.property.1.1
      have h₁ : Icc a (min (pick s hs).val t.val) ⊆ Icc a (pick s hs).val :=
        Icc_subset_Icc le_rfl (min_le_left _ _)
      have h₂ : Icc a (min (pick s hs).val t.val) ⊆ Icc a t.val :=
        Icc_subset_Icc le_rfl (min_le_right _ _)
      exact eqOn_lifts_of_initial hf hmin ((hlift _).1.mono h₁) ((hlift t).1.mono h₂)
        ((hlift _).2.2.mono h₁) ((hlift t).2.2.mono h₂)
        ((hlift _).2.1.trans (hlift t).2.1.symm) ⟨hs.1, le_min (hpick s hs).le hst⟩
    have hη : ContinuousOn η (Ico a T) := by
      intro s hs
      let t := pick s hs
      have hst : s < t.val := hpick s hs
      have hmem : Icc a t.val ∈ 𝓝[Ico a T] s := by
        filter_upwards [(eventually_lt_nhds hst).filter_mono nhdsWithin_le_nhds,
          self_mem_nhdsWithin] with r hr hrs
        exact ⟨hrs.1, hr.le⟩
      have hcont := ((hlift t).1 s ⟨hs.1, hst.le⟩).mono_of_mem_nhdsWithin hmem
      apply hcont.congr_of_eventuallyEq
      · filter_upwards [(eventually_lt_nhds hst).filter_mono nhdsWithin_le_nhds,
          self_mem_nhdsWithin] with r hr hrs
        exact hagree t r hrs hr.le
      · exact hagree t s hs hst.le
    have hηa : η a = x := by
      have ha : a ∈ Ico a T := ⟨le_rfl, haT⟩
      exact (hagree (pick a ha) a ha (hpick a ha).le).trans (hlift _).2.1
    have hηf : EqOn (f ∘ η) γ (Ico a T) := by
      intro s hs
      change f (η s) = γ s
      rw [hagree (pick s hs) s hs (hpick s hs).le]
      exact (hlift _).2.2 ⟨hs.1, (hpick s hs).le⟩
    obtain ⟨z, hz, hfz⟩ := exists_tendsto_lift_of_complete g h hf hg hmetric haT
      (hγ.mono (Icc_subset_Icc le_rfl hTle)) hη hηf
    let ηbar : ℝ → M := fun t => if t < T then η t else z
    have hηbar : ContinuousOn ηbar (Icc a T) := continuousOn_close_lift haT.le hη hz
    have hηbar_a : ηbar a = x := by simp only [ηbar, ite_eq_left haT, hηa]
    have hηbar_f : EqOn (f ∘ ηbar) γ (Icc a T) := by
      intro t ht
      by_cases hlt : t < T
      · simpa only [Function.comp_apply, ηbar, ite_eq_left hlt] using hηf ⟨ht.1, hlt⟩
      · have hteq : t = T := le_antisymm ht.2 (le_of_not_gt hlt)
        simpa only [Function.comp_apply, ηbar, hteq, ite_eq_right (lt_irrefl T)] using hfz
    have hTS : T ∈ S := ⟨⟨haT.le, hTle⟩, ηbar, hηbar, hηbar_a, hηbar_f⟩
    have hTeq : T = b := by
      apply le_antisymm hTle
      by_contra hnot
      have hTb : T < b := lt_of_not_ge hnot
      obtain ⟨u, hu, ζ, hζ, hζa, hζf⟩ := exists_lift_right_extension hf haT.le hTb
        hγ.continuousOn hηbar hηbar_a hηbar_f
      have huS : u ∈ S := ⟨⟨haT.le.trans hu.1.le, hu.2⟩, ζ, hζ, hζa, hζf⟩
      exact (not_lt_of_ge (le_csSup hSbdd huS)) hu.1
    simpa only [hTeq] using hTS.2
  obtain ⟨η, hη, hηa, hηf⟩ := hex
  refine ⟨η, contMDiffOn_lift hf hγ hη hηf, hηa, hηf, ?_⟩
  intro ζ hζ hζa hζf
  exact eqOn_lifts_of_initial hf hab hζ hη hζf hηf (hζa.trans hηa.symm)

end DifferentialGeometry.Geometry.Riemannian
