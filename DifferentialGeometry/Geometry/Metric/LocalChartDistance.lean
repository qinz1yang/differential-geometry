import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter Set MeasureTheory DifferentialGeometry
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mapsTo_of_riemannianEDistOf_add_pathELength_lt
    (g : SmoothRiemannianMetric I M) (p : M) (s : Set M) (R : ℝ≥0∞)
    (hs : {q | riemannianEDistOf g p q < R} ⊆ s)
    (γ : ℝ → M) (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc 0 1)) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    riemannianEDistOf g p (γ 0) + pathELength I γ 0 1 < R →
      MapsTo γ (Icc 0 1) s := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro hshort t ht
  apply hs
  change riemannianEDist I p (γ t) < R
  change riemannianEDist I p (γ 0) + pathELength I γ 0 1 < R at hshort
  have hprefix : riemannianEDist I (γ 0) (γ t) ≤ pathELength I γ 0 t :=
    riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc le_rfl ht.2))
      rfl rfl ht.1
  calc
    riemannianEDist I p (γ t) ≤
        riemannianEDist I p (γ 0) + riemannianEDist I (γ 0) (γ t) :=
      riemannianEDist_triangle
    _ ≤ riemannianEDist I p (γ 0) + pathELength I γ 0 t := add_le_add le_rfl hprefix
    _ ≤ riemannianEDist I p (γ 0) + pathELength I γ 0 1 :=
      add_le_add le_rfl (pathELength_mono (I := I) (γ := γ) le_rfl ht.2)
    _ < R := hshort

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pos_short_path_mapsTo [RegularSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) (s : Set M) (hs : s ∈ 𝓝 p) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ (γ : ℝ → M),
      ContMDiffOn 𝓘(ℝ) I 1 γ (Icc 0 1) →
      riemannianEDistOf g p (γ 0) < δ → pathELength I γ 0 1 < δ →
      MapsTo γ (Icc 0 1) s := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  obtain ⟨c, hc, hball⟩ := setOfPred_riemannianEDist_lt_subset_nhds I hs
  refine ⟨c / 3, by positivity, ?_⟩
  intro γ hγ hstart hlength
  apply mapsTo_of_riemannianEDistOf_add_pathELength_lt g p s c hball γ hγ
  have hsum : ((c / 3 : ℝ≥0) : ℝ≥0∞) + (c / 3 : ℝ≥0) < (c : ℝ≥0∞) := by
    exact_mod_cast (show c / 3 + c / 3 < c by linarith)
  exact (ENNReal.add_lt_add hstart hlength).trans hsum

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eventually_tangent_transport_le
    (g : SmoothRiemannianMetric I M) (p : M) {K : ℝ} (hK : 1 < K) :
    let e := trivializationAt E (TangentSpace I) p
    ∀ᶠ y in 𝓝 p, y ∈ (chartAt H p).source ∧
      (∀ v : TangentSpace I y,
        Real.sqrt (g.inner p
          (e.symmL ℝ p (e.continuousLinearMapAt ℝ y v))
          (e.symmL ℝ p (e.continuousLinearMapAt ℝ y v))) ≤
            K * Real.sqrt (g.inner y v v)) ∧
      ∀ v : TangentSpace I p,
        Real.sqrt (g.inner y
          (e.symmL ℝ y (e.continuousLinearMapAt ℝ p v))
          (e.symmL ℝ y (e.continuousLinearMapAt ℝ p v))) ≤
            K * Real.sqrt (g.inner p v v) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let e := trivializationAt E (TangentSpace I) p
  filter_upwards [chart_source_mem_nhds H p,
    eventually_norm_symmL_trivializationAt_self_comp_lt E (TangentSpace I) p hK,
    eventually_norm_symmL_trivializationAt_comp_self_lt E (TangentSpace I) p hK]
    with y hy hforward hbackward
  refine ⟨hy, ?_, ?_⟩
  · intro v
    have h := ((e.symmL ℝ p).comp (e.continuousLinearMapAt ℝ y)).le_opNorm v
    have h' := h.trans (mul_le_mul_of_nonneg_right hforward.le (norm_nonneg v))
    simp only [ContinuousLinearMap.comp_apply, norm_eq_sqrt_real_inner] at h'
    convert h' using 1 <;> rfl
  · intro v
    have h := ((e.symmL ℝ y).comp (e.continuousLinearMapAt ℝ p)).le_opNorm v
    have h' := h.trans (mul_le_mul_of_nonneg_right hbackward.le (norm_nonneg v))
    simp only [ContinuousLinearMap.comp_apply, norm_eq_sqrt_real_inner] at h'
    convert h' using 1 <;> rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem chart_displacement_le_pathELength
    (g : SmoothRiemannianMetric I M) (p : M) {K : ℝ} (hK : 0 ≤ K)
    (γ : ℝ → M) (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc 0 1))
    (hchart : MapsTo γ (Icc 0 1) (chartAt H p).source)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace I (γ t),
      let e := trivializationAt E (TangentSpace I) p
      Real.sqrt (g.inner p
        (e.symmL ℝ p (e.continuousLinearMapAt ℝ (γ t) v))
        (e.symmL ℝ p (e.continuousLinearMapAt ℝ (γ t) v))) ≤
          K * Real.sqrt (g.inner (γ t) v v)) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let e := trivializationAt E (TangentSpace I) p
    let w := e.symmL ℝ p (extChartAt I p (γ 1) - extChartAt I p (γ 0))
    ENNReal.ofReal (Real.sqrt (g.inner p w w)) ≤
      ENNReal.ofReal K * pathELength I γ 0 1 := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let e := trivializationAt E (TangentSpace I) p
  let S := e.symmL ℝ p
  have norm_g (y : M) (v : TangentSpace I y) :
      ‖v‖ = Real.sqrt (g.inner y v v) := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  let ξ := extChartAt I p ∘ γ
  let Γ := S ∘ ξ
  have hξ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 ξ (Icc 0 1) :=
    contMDiffOn_extChartAt.comp hγ hchart
  have hξ' : ContDiffOn ℝ 1 ξ (Icc 0 1) := contMDiffOn_iff_contDiffOn.mp hξ
  have hΓ : ContDiffOn ℝ 1 Γ (Icc 0 1) := S.contDiff.comp_contDiffOn hξ'
  change ENNReal.ofReal (Real.sqrt (g.inner p
    (S (ξ 1 - ξ 0)) (S (ξ 1 - ξ 0)))) ≤ _
  rw [← norm_g p _, ofReal_norm]
  have hdisplacement : S (ξ 1 - ξ 0) = Γ 1 - Γ 0 := by simp [Γ]
  rw [hdisplacement]
  calc
    ‖Γ 1 - Γ 0‖ₑ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖derivWithin Γ (Icc 0 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hΓ zero_le_one
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1,
        ENNReal.ofReal K * ‖mfderivWithin 𝓘(ℝ) I γ (Icc 0 1) t 1‖ₑ := by
      apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hunique := uniqueDiffOn_Icc zero_lt_one t ht
      have hder : derivWithin Γ (Icc 0 1) t =
          S (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) ξ (Icc 0 1) t 1) := by
        rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
        exact congrArg (fun L : ℝ →L[ℝ] TangentSpace I p => L 1)
          ((S.hasFDerivAt.comp_hasFDerivWithinAt t
            (hξ'.differentiableOn one_ne_zero t ht).hasFDerivWithinAt).fderivWithin hunique)
      have hξder : mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) ξ (Icc 0 1) t =
          (mfderiv I 𝓘(ℝ, E) (extChartAt I p) (γ t)).comp
            (mfderivWithin 𝓘(ℝ) I γ (Icc 0 1) t) := by
        apply mfderiv_comp_mfderivWithin
        · exact mdifferentiableAt_extChartAt (hchart ht)
        · exact hγ.mdifferentiableOn one_ne_zero t ht
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact hunique
      rw [hder, hξder, ContinuousLinearMap.comp_apply,
        ← TangentBundle.continuousLinearMapAt_trivializationAt (hchart ht)]
      have hnorm : ‖S (e.continuousLinearMapAt ℝ (γ t)
          (mfderivWithin 𝓘(ℝ) I γ (Icc 0 1) t 1))‖ ≤
          K * ‖mfderivWithin 𝓘(ℝ) I γ (Icc 0 1) t 1‖ := by
        simpa only [norm_g] using hbound t ht _
      have hn := ENNReal.ofReal_le_ofReal hnorm
      simp only [ENNReal.ofReal_mul hK, ofReal_norm] at hn
      convert hn using 1; rfl
    _ = ENNReal.ofReal K * pathELength I γ 0 1 := by
      rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        pathELength_eq_lintegral_mfderivWithin_Icc]

end DifferentialGeometry.Geometry.Metric
