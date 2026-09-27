import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

open Set Filter Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

private theorem exists_first_level {α : Type*} [LinearOrder α]
    [TopologicalSpace α] [OrderClosedTopology α]
    {f : ℝ → α} {a b : ℝ} {r : α}
    (hf : Continuous f) (hab : a ≤ b) (ha : f a < r) (hb : r ≤ f b) :
    ∃ t ∈ Icc a b, f t = r ∧ ∀ s ∈ Icc a t, f s ≤ r := by
  let S : Set ℝ := Icc a b ∩ f ⁻¹' Ici r
  have hS : IsCompact S := isCompact_Icc.inter_right (isClosed_Ici.preimage hf)
  have hSne : S.Nonempty := ⟨b, ⟨⟨hab, le_rfl⟩, hb⟩⟩
  obtain ⟨t, ht, hmin⟩ := hS.exists_isMinOn hSne continuous_id.continuousOn
  have htlo : a ≤ t := ht.1.1
  have hthi : t ≤ b := ht.1.2
  have htlevel : r ≤ f t := ht.2
  obtain ⟨u, hu, hur⟩ := intermediate_value_Icc htlo hf.continuousOn ⟨ha.le, htlevel⟩
  have htu : t ≤ u := hmin ⟨⟨hu.1, hu.2.trans hthi⟩, hur.ge⟩
  have hut : u = t := hu.2.antisymm htu
  refine ⟨t, ht.1, hut ▸ hur, ?_⟩
  intro s hs
  rcases hs.2.eq_or_lt with rfl | hst
  · exact (hut ▸ hur).le
  · by_contra hn
    have hrs : r < f s := lt_of_not_ge hn
    have hts : t ≤ s := hmin ⟨⟨hs.1, hs.2.trans hthi⟩, hrs.le⟩
    exact (not_lt_of_ge hts) hst

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def metricPathELength (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Icc a b, ENNReal.ofReal (Real.sqrt
    (g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem pathELength_eq_metricPathELength
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) :
    letI : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    pathELength I γ a b = metricPathELength g γ a b := by
  let : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  rw [pathELength_eq_lintegral_mfderiv_Icc, metricPathELength]
  congr 1
  funext s
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem riemannianEDistOf_le_metricPathELength
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
    riemannianEDistOf (I := I) g (γ a) (γ b) ≤ metricPathELength g γ a b := by
  let : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  change riemannianEDist I (γ a) (γ b) ≤ _
  rw [← pathELength_eq_metricPathELength g γ a b]
  exact riemannianEDist_le_pathELength hγ rfl rfl hab

private theorem metricPathELength_mono
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {a b a' b' : ℝ}
    (ha : a' ≤ a) (hb : b ≤ b') :
    metricPathELength g γ a b ≤ metricPathELength g γ a' b' := by
  exact lintegral_mono_set (Icc_subset_Icc ha hb)

private theorem mul_metricPathELength_le_of_metric_lower
    (g h : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b c : ℝ}
    (hc : 0 ≤ c)
    (hbound : ∀ s ∈ Icc a b, ∀ v : TangentSpace I (γ s),
      c ^ 2 * g.inner (γ s) v v ≤ h.inner (γ s) v v) :
    ENNReal.ofReal c * metricPathELength g γ a b ≤ metricPathELength h γ a b := by
  rw [metricPathELength, metricPathELength, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro s hs
  have hq := Real.sqrt_le_sqrt (hbound s hs (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)))
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc] at hq
  simpa only [ENNReal.ofReal_mul hc] using ENNReal.ofReal_le_ofReal hq

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem riemannianEDistOf_le_metricPathELength_of_metric_lower_on_ball
    [RegularSpace M]
    (g h : SmoothRiemannianMetric I M) {γ : ℝ → M} (O : M)
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hbound : ∀ y : M, riemannianEDistOf (I := I) g O y ≤ ENNReal.ofReal R →
      ∀ v : TangentSpace I y, c ^ 2 * g.inner y v v ≤ h.inner y v v)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (hγ0 : γ 0 = O)
    (hlen : metricPathELength h γ 0 1 < ENNReal.ofReal (c * R)) :
    ENNReal.ofReal c * riemannianEDistOf (I := I) g O (γ 1) ≤
      metricPathELength h γ 0 1 := by
  have hgcont : Continuous (fun y => riemannianEDistOf (I := I) g O y) := by
    let : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
    let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    exact continuous_const.edist continuous_id
  have hstays : ∀ s ∈ Icc (0 : ℝ) 1,
      riemannianEDistOf (I := I) g O (γ s) ≤ ENNReal.ofReal R := by
    intro s hs
    by_contra hn
    have hslevel : ENNReal.ofReal R ≤ riemannianEDistOf (I := I) g O (γ s) :=
      (lt_of_not_ge hn).le
    obtain ⟨t, ht, htlevel, htstay⟩ := exists_first_level
      (hgcont.comp hγ.continuous) hs.1
      (show riemannianEDistOf (I := I) g O (γ 0) < ENNReal.ofReal R from by
        rw [hγ0, riemannianEDistOf_self]
        exact ENNReal.ofReal_pos.2 hR) hslevel
    have hdist := riemannianEDistOf_le_metricPathELength g ht.1 hγ.contMDiffOn
    dsimp only [Function.comp_def] at htlevel
    rw [hγ0, htlevel] at hdist
    have hlencomp := mul_metricPathELength_le_of_metric_lower g h hc.le
      (fun u hu v => hbound (γ u) (htstay u hu) v)
    have hle : ENNReal.ofReal (c * R) ≤ metricPathELength h γ 0 1 := by
      rw [ENNReal.ofReal_mul hc.le]
      exact (mul_le_mul_of_nonneg_left hdist (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal c)).trans
        (hlencomp.trans (metricPathELength_mono h γ le_rfl (ht.2.trans hs.2)))
    exact (not_lt_of_ge hle) hlen
  have hdist := riemannianEDistOf_le_metricPathELength g zero_le_one hγ.contMDiffOn
  rw [hγ0] at hdist
  exact (mul_le_mul_of_nonneg_left hdist (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal c)).trans
    (mul_metricPathELength_le_of_metric_lower g h hc.le (fun s hs v => hbound (γ s) (hstays s hs) v))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_le_of_metric_lower_on_ball
    [RegularSpace M]
    (g h : SmoothRiemannianMetric I M) (O x : M)
    {c R : ℝ} (hc : 0 < c)
    (hbound : ∀ y : M, riemannianEDistOf (I := I) g O y ≤ ENNReal.ofReal R →
      ∀ v : TangentSpace I y, c ^ 2 * g.inner y v v ≤ h.inner y v v)
    (hdist : riemannianEDistOf (I := I) h O x < ENNReal.ofReal (c * R)) :
    riemannianEDistOf (I := I) g O x ≤
      ENNReal.ofReal ((riemannianEDistOf (I := I) h O x).toReal / c) := by
  have hR : 0 < R := (mul_pos_iff_of_pos_left hc).mp
    (ENNReal.ofReal_pos.mp (bot_le.trans_lt hdist))
  have hfin : riemannianEDistOf (I := I) h O x ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hdist.le
  have hcle : ENNReal.ofReal c * riemannianEDistOf (I := I) g O x ≤
      riemannianEDistOf (I := I) h O x := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro r hr
    obtain ⟨s, hds, hsr⟩ := exists_between (lt_min hr hdist)
    let : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨h.toRiemannianMetric⟩
    obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ :=
      exists_lt_locally_constant_of_riemannianEDist_lt hds zero_lt_one
    rw [pathELength_eq_metricPathELength h γ 0 1] at hlen
    have hle := riemannianEDistOf_le_metricPathELength_of_metric_lower_on_ball
      g h O hc hR hbound hγ hγ0 (hlen.trans (hsr.trans_le (min_le_right _ _)))
    rw [hγ1] at hle
    exact hle.trans (hlen.le.trans (hsr.le.trans (min_le_left _ _)))
  rw [ENNReal.ofReal_div_of_pos hc, ENNReal.ofReal_toReal hfin]
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hc).ne')
    (Or.inl ENNReal.ofReal_ne_top)).2
  simpa only [mul_comm] using hcle

end DifferentialGeometry.Geometry.Riemannian
