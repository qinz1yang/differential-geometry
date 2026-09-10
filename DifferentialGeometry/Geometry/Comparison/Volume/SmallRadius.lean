import DifferentialGeometry.Geometry.Comparison.Volume.AsymptoticVolumeRatio
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Local

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace Poincare.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]


theorem volume_unitBall_eq_ofReal_euclideanUnitBallVolume :
    (volume : Measure E) (Metric.ball (0 : E) 1) =
      ENNReal.ofReal (euclideanUnitBallVolume (Module.finrank ℝ E)) := by
  let _ : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  rw [InnerProductSpace.volume_ball]
  simp [euclideanUnitBallVolume]

theorem framedBall_eq_small_smooth [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R : ℝ} (hR : 0 < R)
    (hRexp : R < expDiffeoRadius (I := I) g hEnorm p) :
    framedExpDiffeo (I := I) g p '' Metric.ball (0 : E) R =
      smallNormalBall (I := I) p R := by
  classical
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzNorm : ‖z‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hzExp : ‖z‖ < expDiffeoRadius (I := I) g hEnorm p :=
      hzNorm.trans hRexp
    have hvExp : Real.sqrt
        (g.inner p (normalFrame (I := I) g p z)
          (normalFrame (I := I) g p z)) <
        expDiffeoRadius (I := I) g hEnorm p := by
      simpa only [normalFrame_sqrt] using hzExp
    have hvSrc := expDiffeo_mem_of_lt (I := I) g hEnorm p hvExp
    have hvGp : Real.sqrt
        (g.inner p (normalFrame (I := I) g p z)
          (normalFrame (I := I) g p z)) < metricCoerciveExpRadius (I := I) g p :=
      hvExp.trans_le (min_le_right _ _)
    have hzFramedSrc : z ∈ (framedExpDiffeo (I := I) g p).source := by
      rw [framedExp_source]
      exact hvSrc
    rw [mem_smallNormalBall, framedExp_eq_expMap (I := I) g p hzFramedSrc,
      framedExpMap_apply,
      edist_exp_eq_radius (I := I) g p hEnorm hvGp,
      normalFrame_sqrt]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg z)).2 hzNorm
  · intro hq
    obtain ⟨v, hvExp, hvLen⟩ :=
      hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm p q
    have hdist : (riemannianEDist I p q).toReal < R := by
      have hlt := (ENNReal.toReal_lt_toReal
        (riemannianEDist_ne_top (I := I) p q) ENNReal.ofReal_ne_top).2 hq
      simpa only [ENNReal.toReal_ofReal hR.le] using hlt
    have hvSmall : Real.sqrt (g.inner p (v : E) (v : E)) <
        expDiffeoRadius (I := I) g hEnorm p := by
      rw [hvLen]
      exact hdist.trans hRexp
    let z : E := (normalFrame (I := I) g p).symm v
    have hzFrame : normalFrame (I := I) g p z = v := by
      exact (normalFrame (I := I) g p).apply_symm_apply v
    have hzNorm : ‖z‖ = Real.sqrt (g.inner p (v : E) (v : E)) := by
      have h := normalFrame_sqrt (I := I) g p z
      rw [hzFrame] at h
      exact h.symm
    have hzBall : z ∈ Metric.ball (0 : E) R := by
      rw [Metric.mem_ball, dist_zero_right, hzNorm, hvLen]
      exact hdist
    refine ⟨z, hzBall, ?_⟩
    rw [framedExp_apply, hzFrame]
    calc
      expMapDiffeo (I := I) g p
          (tangentSpaceModelContinuousLinearEquiv (I := I) p v) =
          expMapIntrinsic (I := I) g hEnorm p v := by
        with_unfolding_all
          exact expDiffeo_eq_intr (I := I) g hEnorm p hvSmall
      _ = q := hvExp

theorem ballVolume_eq_framedExp_image [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R : ℝ} (hR : 0 < R)
    (hRexp : R < expDiffeoRadius (I := I) g hEnorm p) :
    ballVolume g p R =
      riemannianVolumeMeasure (I := I) (M := M) g
        (framedExpDiffeo (I := I) g p '' Metric.ball (0 : E) R) := by
  rw [framedBall_eq_small_smooth (I := I) g hEnorm p hR hRexp]
  unfold ballVolume
  congr 1

theorem exists_ballVolume_chart_ratio [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ,
      c = paramDensity (I := I) g (framedExpDiffeo (I := I) g p) 0 ∧
      0 < c ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ {r : ℝ}, 0 < r → r < ρ →
        ENNReal.ofReal ((1 - ε) * c) *
            (ENNReal.ofReal (r ^ Module.finrank ℝ E) *
              (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
          ballVolume g p r ∧
        ballVolume g p r ≤
          ENNReal.ofReal ((1 + ε) * c) *
            (ENNReal.ofReal (r ^ Module.finrank ℝ E) *
              (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  let Ψ := framedExpDiffeo (I := I) g p
  let f : E → ℝ := paramDensity (I := I) g Ψ
  have hzero : (0 : E) ∈ Ψ.source := by
    simpa only [Ψ] using zero_mem_framedExp_source (I := I) g p
  have hfpos : 0 < f 0 := by
    exact paramDensity_pos (I := I) g Ψ hzero
  refine ⟨f 0, by rfl, hfpos, ?_⟩
  have hcont : ContinuousWithinAt f Ψ.source 0 := by
    exact (paramDensity_contOn (I := I) g Ψ) 0 hzero
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousWithinAt_iff.mp hcont) (ε * f 0) (mul_pos hε hfpos)
  obtain ⟨s, hs, hsource⟩ := exists_framed_ball (I := I) g p
  let e : ℝ := expDiffeoRadius (I := I) g hEnorm p
  let ρ : ℝ := min δ (min s e)
  have he : 0 < e := by
    simpa only [e] using expDiffeoRadius_pos (I := I) g hEnorm p
  have hρ : 0 < ρ := by
    simpa only [ρ] using lt_min hδ (lt_min hs he)
  refine ⟨ρ, hρ, ?_⟩
  intro r hr hrρ
  have hrδ : r < δ := hrρ.trans_le (min_le_left _ _)
  have hrs : r < s :=
    hrρ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hre : r < expDiffeoRadius (I := I) g hEnorm p := by
    simpa only [e] using
      hrρ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hrsource : Metric.ball (0 : E) r ⊆ Ψ.source := by
    simpa only [Ψ] using (Metric.ball_subset_ball hrs.le).trans hsource
  have hdens (z : E) (hz : z ∈ Metric.ball (0 : E) r) :
      (1 - ε) * f 0 ≤ f z ∧ f z ≤ (1 + ε) * f 0 := by
    have hzδ : dist z (0 : E) < δ :=
      (Metric.mem_ball.mp hz).trans hrδ
    have hzclose := hclose (hrsource hz) hzδ
    rw [Real.dist_eq] at hzclose
    exact ⟨by nlinarith [neg_lt_of_abs_lt hzclose],
      by nlinarith [lt_of_abs_lt hzclose]⟩
  have hlow :
      ENNReal.ofReal ((1 - ε) * f 0) *
          (modelHaar (E := E)) (Metric.ball (0 : E) r) ≤
        riemannianVolumeMeasure (I := I) (M := M) g
          (Ψ '' Metric.ball (0 : E) r) := by
    exact param_vol_ge (I := I) g Ψ measurableSet_ball hrsource
      (fun z hz => (hdens z hz).1)
  have hupp :
      riemannianVolumeMeasure (I := I) (M := M) g
          (Ψ '' Metric.ball (0 : E) r) ≤
        ENNReal.ofReal ((1 + ε) * f 0) *
          (modelHaar (E := E)) (Metric.ball (0 : E) r) := by
    rw [riemannianVolumeMeasure_image_param_eq
      (I := I) g Ψ measurableSet_ball hrsource]
    calc
      (∫⁻ z in Metric.ball (0 : E) r, ENNReal.ofReal (f z)
          ∂(modelHaar (E := E))) ≤
          ∫⁻ _z in Metric.ball (0 : E) r, ENNReal.ofReal ((1 + ε) * f 0)
            ∂(modelHaar (E := E)) := by
        refine MeasureTheory.setLIntegral_mono' measurableSet_ball ?_
        intro z hz
        exact ENNReal.ofReal_le_ofReal (hdens z hz).2
      _ = ENNReal.ofReal ((1 + ε) * f 0) *
          (modelHaar (E := E)) (Metric.ball (0 : E) r) := by
        rw [MeasureTheory.setLIntegral_const]
  have hball : ballVolume g p r =
      riemannianVolumeMeasure (I := I) (M := M) g
        (Ψ '' Metric.ball (0 : E) r) := by
    simpa only [Ψ] using
      ballVolume_eq_framedExp_image (I := I) g hEnorm p hr hre
  constructor
  · rw [hball]
    simpa only [f, Ψ, modelHaar_ball (E := E) hr] using hlow
  · rw [hball]
    simpa only [f, Ψ, modelHaar_ball (E := E) hr] using hupp

theorem exists_ballVolume_euclidean_ratio [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {r : ℝ}, 0 < r → r < ρ →
      ENNReal.ofReal (1 - ε) *
          (ENNReal.ofReal (r ^ Module.finrank ℝ E) *
            (volume : Measure E) (Metric.ball (0 : E) 1)) ≤
        ballVolume g p r ∧
      ballVolume g p r ≤
        ENNReal.ofReal (1 + ε) *
          (ENNReal.ofReal (r ^ Module.finrank ℝ E) *
            (volume : Measure E) (Metric.ball (0 : E) 1)) := by
  obtain ⟨c, hc, _hcpos, ρ, hρ, hratio⟩ :=
    exists_ballVolume_chart_ratio (I := I) g hEnorm p ε hε
  have hhaar :
      ENNReal.ofReal c * (modelHaar (E := E)) (Metric.ball (0 : E) 1) =
        (volume : Measure E) (Metric.ball (0 : E) 1) := by
    have h := congrArg (fun μ : Measure E => μ (Metric.ball (0 : E) 1))
      (framedDens_haar (I := I) g p)
    simpa only [Measure.smul_apply, smul_eq_mul, hc] using h
  have hoflow : ENNReal.ofReal ((1 - ε) * c) =
      ENNReal.ofReal (1 - ε) * ENNReal.ofReal c :=
    ENNReal.ofReal_mul (sub_nonneg.mpr hε1.le)
  have hofupp : ENNReal.ofReal ((1 + ε) * c) =
      ENNReal.ofReal (1 + ε) * ENNReal.ofReal c :=
    ENNReal.ofReal_mul (by positivity)
  refine ⟨ρ, hρ, ?_⟩
  intro r hr hrρ
  obtain ⟨hlow, hupp⟩ := hratio hr hrρ
  constructor
  · calc
      ENNReal.ofReal (1 - ε) *
          (ENNReal.ofReal (r ^ Module.finrank ℝ E) *
            (volume : Measure E) (Metric.ball (0 : E) 1)) =
          ENNReal.ofReal ((1 - ε) * c) *
            (ENNReal.ofReal (r ^ Module.finrank ℝ E) *
              (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
        rw [hoflow, ← hhaar]
        simp only [mul_assoc, mul_comm, mul_left_comm]
      _ ≤ ballVolume g p r := hlow
  · calc
      ballVolume g p r ≤
          ENNReal.ofReal ((1 + ε) * c) *
            (ENNReal.ofReal (r ^ Module.finrank ℝ E) *
              (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := hupp
      _ = ENNReal.ofReal (1 + ε) *
          (ENNReal.ofReal (r ^ Module.finrank ℝ E) *
            (volume : Measure E) (Metric.ball (0 : E) 1)) := by
        rw [hofupp, ← hhaar]
        simp only [mul_assoc, mul_comm, mul_left_comm]

theorem eventually_ballVolume_div_modelVolume_zero_mem_Icc
    [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ballVolume g p r /
          ENNReal.ofReal (modelVolume 0 (Module.finrank ℝ E) r) ∈
        Set.Icc (ENNReal.ofReal (1 - ε)) (ENNReal.ofReal (1 + ε)) := by
  let n : ℕ := Module.finrank ℝ E
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  obtain ⟨ρ, hρ, hsmall⟩ :=
    exists_ballVolume_euclidean_ratio (I := I) g hEnorm p ε hε hε1
  have hevent : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ρ :=
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left) (Iio_mem_nhds hρ)
  filter_upwards [self_mem_nhdsWithin, hevent] with r hr hrρ
  have hmodel : ENNReal.ofReal (modelVolume 0 n r) =
      ENNReal.ofReal (r ^ n) * (volume : Measure E) (Metric.ball (0 : E) 1) := by
    rw [modelVolume_zero n r hn,
      volume_unitBall_eq_ofReal_euclideanUnitBallVolume (E := E),
      ENNReal.ofReal_mul (euclideanUnitBallVolume_pos n).le]
    ac_rfl
  have hmodel_pos : 0 < ENNReal.ofReal (modelVolume 0 n r) := by
    exact ENNReal.ofReal_pos.2
      (modelVolume_pos hn hr ⟨hr.le, by simp⟩)
  obtain ⟨hlow, hupp⟩ := hsmall hr hrρ
  rw [← hmodel] at hlow hupp
  constructor
  · exact (ENNReal.le_div_iff_mul_le
      (Or.inl hmodel_pos.ne') (Or.inl ENNReal.ofReal_ne_top)).2 hlow
  · exact (ENNReal.div_le_iff hmodel_pos.ne' ENNReal.ofReal_ne_top).2 hupp

theorem tendsto_ballVolume_div_modelVolume_zero [ConnectedSpace M]
    [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    Tendsto (fun r : ℝ => ballVolume g p r /
      ENNReal.ofReal (modelVolume 0 (Module.finrank ℝ E) r))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hatop : a ≠ ⊤ := by
      exact ne_top_of_lt (ha.trans ENNReal.one_lt_top)
    have hareal : a.toReal < 1 := by
      have h := (ENNReal.toReal_lt_toReal hatop ENNReal.one_ne_top).2 ha
      simpa using h
    let ε : ℝ := min (1 / 2 : ℝ) ((1 - a.toReal) / 2)
    have hgap : 0 < 1 - a.toReal := sub_pos.2 hareal
    have hε : 0 < ε := by
      exact lt_min (by norm_num) (div_pos hgap (by norm_num))
    have hεhalf : ε ≤ (1 / 2 : ℝ) := min_le_left _ _
    have hε1 : ε < 1 := by linarith
    have haε : a < ENNReal.ofReal (1 - ε) := by
      apply (ENNReal.lt_ofReal_iff_toReal_lt hatop).2
      have hεle : ε ≤ (1 - a.toReal) / 2 := min_le_right _ _
      linarith
    filter_upwards
      [eventually_ballVolume_div_modelVolume_zero_mem_Icc
        (I := I) g hEnorm p hε hε1] with r hr
    exact haε.trans_le hr.1
  · intro b hb
    by_cases hbtop : b = ⊤
    · subst b
      have hε : (0 : ℝ) < 1 / 2 := by norm_num
      have hε1 : (1 / 2 : ℝ) < 1 := by norm_num
      filter_upwards
        [eventually_ballVolume_div_modelVolume_zero_mem_Icc
          (I := I) g hEnorm p hε hε1] with r hr
      exact hr.2.trans_lt ENNReal.ofReal_lt_top
    · have hbreal : 1 < b.toReal := by
        have h := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hbtop).2 hb
        simpa using h
      let ε : ℝ := min (1 / 2 : ℝ) ((b.toReal - 1) / 2)
      have hgap : 0 < b.toReal - 1 := sub_pos.2 hbreal
      have hε : 0 < ε := by
        exact lt_min (by norm_num) (div_pos hgap (by norm_num))
      have hεhalf : ε ≤ (1 / 2 : ℝ) := min_le_left _ _
      have hε1 : ε < 1 := by linarith
      have hεb : ENNReal.ofReal (1 + ε) < b := by
        apply (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hbtop).2
        have hεle : ε ≤ (b.toReal - 1) / 2 := min_le_right _ _
        linarith
      filter_upwards
        [eventually_ballVolume_div_modelVolume_zero_mem_Icc
          (I := I) g hEnorm p hε hε1] with r hr
      exact hr.2.trans_lt hεb

theorem eventually_modelVolume_between_euclidean_multiples
    (K : ℝ) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (1 - δ) ^ (n - 1) * modelVolume 0 n r ≤ modelVolume K n r ∧
      modelVolume K n r ≤ (1 + δ) ^ (n - 1) * modelVolume 0 n r := by
  have hratio := modelRadiusRatio_tendsto K
  have hlower : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      1 - δ < modelRadius K t / t :=
    (tendsto_order.1 hratio).1 (1 - δ) (by linarith)
  have hupper : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      modelRadius K t / t < 1 + δ :=
    (tendsto_order.1 hratio).2 (1 + δ) (by linarith)
  obtain ⟨ρ, hρ, hρsub⟩ :=
    mem_nhdsGT_iff_exists_Ioc_subset.1 (hlower.and hupper)
  have hρevent : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ρ :=
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left) (Iio_mem_nhds hρ)
  filter_upwards [self_mem_nhdsWithin, hρevent] with r hr hrρ
  let d : ℕ := n - 1
  have hfactor : 0 ≤ (n : ℝ) * euclideanUnitBallVolume n :=
    mul_nonneg (Nat.cast_nonneg n) (euclideanUnitBallVolume_pos n).le
  have hleft_cont : Continuous (fun t : ℝ =>
      (1 - δ) ^ d * modelArea 0 n t) :=
    continuous_const.mul (modelArea_continuous 0 n)
  have hright_cont : Continuous (fun t : ℝ =>
      (1 + δ) ^ d * modelArea 0 n t) :=
    continuous_const.mul (modelArea_continuous 0 n)
  have hmodel_cont : Continuous (modelArea K n) := modelArea_continuous K n
  have hpoint (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) r) :
      (1 - δ) ^ d * modelArea 0 n t ≤ modelArea K n t ∧
      modelArea K n t ≤ (1 + δ) ^ d * modelArea 0 n t := by
    have htρ : t ∈ Set.Ioc (0 : ℝ) ρ := ⟨ht.1, ht.2.trans hrρ |>.le⟩
    have hbounds := hρsub htρ
    have hlowrad : (1 - δ) * t ≤ modelRadius K t := by
      have h := mul_lt_mul_of_pos_right hbounds.1 ht.1
      rw [div_mul_cancel₀ _ ht.1.ne'] at h
      exact h.le
    have huprad : modelRadius K t ≤ (1 + δ) * t := by
      have h := mul_lt_mul_of_pos_right hbounds.2 ht.1
      rw [div_mul_cancel₀ _ ht.1.ne'] at h
      exact h.le
    have hlowbase : 0 ≤ (1 - δ) * t :=
      mul_nonneg (sub_nonneg.mpr hδ1.le) ht.1.le
    have hmodelbase : 0 ≤ modelRadius K t := hlowbase.trans hlowrad
    have hlowpow : ((1 - δ) * t) ^ d ≤ modelRadius K t ^ d :=
      pow_le_pow_left₀ hlowbase hlowrad d
    have huppow : modelRadius K t ^ d ≤ ((1 + δ) * t) ^ d :=
      pow_le_pow_left₀ hmodelbase huprad d
    constructor
    · calc
        (1 - δ) ^ d * modelArea 0 n t =
            ((n : ℝ) * euclideanUnitBallVolume n) * ((1 - δ) * t) ^ d := by
          simp only [modelArea, modelRadius_zero, d, mul_pow]
          ring
        _ ≤ ((n : ℝ) * euclideanUnitBallVolume n) *
            modelRadius K t ^ d := mul_le_mul_of_nonneg_left hlowpow hfactor
        _ = modelArea K n t := by simp only [modelArea, d]
    · calc
        modelArea K n t = ((n : ℝ) * euclideanUnitBallVolume n) *
            modelRadius K t ^ d := by simp only [modelArea, d]
        _ ≤ ((n : ℝ) * euclideanUnitBallVolume n) *
            ((1 + δ) * t) ^ d := mul_le_mul_of_nonneg_left huppow hfactor
        _ = (1 + δ) ^ d * modelArea 0 n t := by
          simp only [modelArea, modelRadius_zero, d, mul_pow]
          ring
  change
    (1 - δ) ^ d * (∫ t in (0 : ℝ)..r, modelArea 0 n t) ≤
        ∫ t in (0 : ℝ)..r, modelArea K n t ∧
      (∫ t in (0 : ℝ)..r, modelArea K n t) ≤
        (1 + δ) ^ d * ∫ t in (0 : ℝ)..r, modelArea 0 n t
  constructor
  · rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on_of_le_Ioo hr.le
      (hleft_cont.intervalIntegrable 0 r)
      (hmodel_cont.intervalIntegrable 0 r) (fun t ht => (hpoint t ht).1)
  · rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on_of_le_Ioo hr.le
      (hmodel_cont.intervalIntegrable 0 r)
      (hright_cont.intervalIntegrable 0 r) (fun t ht => (hpoint t ht).2)

theorem eventually_modelVolume_div_modelVolume_zero_mem_Icc
    (K : ℝ) {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (modelVolume K n r) /
          ENNReal.ofReal (modelVolume 0 n r) ∈
        Set.Icc (ENNReal.ofReal ((1 - δ) ^ (n - 1)))
          (ENNReal.ofReal ((1 + δ) ^ (n - 1))) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_modelVolume_between_euclidean_multiples K n hδ hδ1]
      with r hr hbounds
  have hden_pos : 0 < ENNReal.ofReal (modelVolume 0 n r) :=
    ENNReal.ofReal_pos.2 (modelVolume_pos hn hr ⟨hr.le, by simp⟩)
  have hlow_nonneg : 0 ≤ (1 - δ) ^ (n - 1) :=
    pow_nonneg (sub_nonneg.mpr hδ1.le) _
  have hupp_nonneg : 0 ≤ (1 + δ) ^ (n - 1) := by positivity
  have hlow := ENNReal.ofReal_le_ofReal hbounds.1
  have hupp := ENNReal.ofReal_le_ofReal hbounds.2
  rw [ENNReal.ofReal_mul hlow_nonneg] at hlow
  rw [ENNReal.ofReal_mul hupp_nonneg] at hupp
  constructor
  · exact (ENNReal.le_div_iff_mul_le
      (Or.inl hden_pos.ne') (Or.inl ENNReal.ofReal_ne_top)).2 hlow
  · exact (ENNReal.div_le_iff hden_pos.ne' ENNReal.ofReal_ne_top).2 hupp

theorem tendsto_modelVolume_div_modelVolume_zero
    (K : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun r : ℝ =>
      ENNReal.ofReal (modelVolume K n r) /
        ENNReal.ofReal (modelVolume 0 n r))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  let d : ℕ := n - 1
  have hlowerFactor :
      Tendsto (fun δ : ℝ => ENNReal.ofReal ((1 - δ) ^ d))
        (𝓝 0) (𝓝 1) := by
    have hcont : Continuous
        (fun δ : ℝ => ENNReal.ofReal ((1 - δ) ^ d)) :=
      ENNReal.continuous_ofReal.comp
        ((continuous_const.sub continuous_id).pow d)
    have ht : Tendsto
        (fun δ : ℝ => ENNReal.ofReal ((1 - δ) ^ d))
        (𝓝 0) (𝓝 (ENNReal.ofReal ((1 - (0 : ℝ)) ^ d))) :=
      hcont.continuousAt
    simpa using ht
  have hupperFactor :
      Tendsto (fun δ : ℝ => ENNReal.ofReal ((1 + δ) ^ d))
        (𝓝 0) (𝓝 1) := by
    have hcont : Continuous
        (fun δ : ℝ => ENNReal.ofReal ((1 + δ) ^ d)) :=
      ENNReal.continuous_ofReal.comp
        ((continuous_const.add continuous_id).pow d)
    have ht : Tendsto
        (fun δ : ℝ => ENNReal.ofReal ((1 + δ) ^ d))
        (𝓝 0) (𝓝 (ENNReal.ofReal ((1 + (0 : ℝ)) ^ d))) :=
      hcont.continuousAt
    simpa using ht
  have hltOne : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 :=
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have haFactor : ∀ᶠ δ in 𝓝 (0 : ℝ),
        a < ENNReal.ofReal ((1 - δ) ^ d) :=
      (tendsto_order.1 hlowerFactor).1 a ha
    have haFactorRight : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        a < ENNReal.ofReal ((1 - δ) ^ d) :=
      haFactor.filter_mono inf_le_left
    obtain ⟨δ, hδ, haδ, hδ1⟩ :=
      (hpos.and (haFactorRight.and hltOne)).exists
    filter_upwards
      [eventually_modelVolume_div_modelVolume_zero_mem_Icc K hn hδ hδ1]
        with r hr
    exact haδ.trans_le hr.1
  · intro b hb
    have hbFactor : ∀ᶠ δ in 𝓝 (0 : ℝ),
        ENNReal.ofReal ((1 + δ) ^ d) < b :=
      (tendsto_order.1 hupperFactor).2 b hb
    have hbFactorRight : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal ((1 + δ) ^ d) < b :=
      hbFactor.filter_mono inf_le_left
    obtain ⟨δ, hδ, hbδ, hδ1⟩ :=
      (hpos.and (hbFactorRight.and hltOne)).exists
    filter_upwards
      [eventually_modelVolume_div_modelVolume_zero_mem_Icc K hn hδ hδ1]
        with r hr
    exact hr.2.trans_lt hbδ

theorem tendsto_ballVolume_div_modelVolume [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (K : ℝ) :
    Tendsto (fun r : ℝ => ballVolume g p r /
      ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) r))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  let n : ℕ := Module.finrank ℝ E
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  let A : ℝ → ℝ≥0∞ := fun r =>
    ballVolume g p r / ENNReal.ofReal (modelVolume 0 n r)
  let B : ℝ → ℝ≥0∞ := fun r =>
    ENNReal.ofReal (modelVolume K n r) /
      ENNReal.ofReal (modelVolume 0 n r)
  have hA : Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [A, n] using
      tendsto_ballVolume_div_modelVolume_zero (I := I) g hEnorm p
  have hB : Tendsto B (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [B] using tendsto_modelVolume_div_modelVolume_zero K hn
  have hdiv : Tendsto (fun r => A r / B r)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using
      ENNReal.Tendsto.div hA (Or.inl one_ne_zero) hB
        (Or.inl ENNReal.one_ne_top)
  have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      A r / B r = ballVolume g p r /
        ENNReal.ofReal (modelVolume K n r) := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_modelRadiusAdmissible K] with r hr hadm
    let C : ℝ≥0∞ := ENNReal.ofReal (modelVolume 0 n r)
    let D : ℝ≥0∞ := ENNReal.ofReal (modelVolume K n r)
    have hC0 : C ≠ 0 := (ENNReal.ofReal_pos.2
      (modelVolume_pos hn hr ⟨hr.le, by simp⟩)).ne'
    have hD0 : D ≠ 0 := (ENNReal.ofReal_pos.2
      (modelVolume_pos hn hr ⟨hr.le, fun hK => (hadm.2 hK).le⟩)).ne'
    have hCt : C ≠ ⊤ := ENNReal.ofReal_ne_top
    have hDt : D ≠ ⊤ := ENNReal.ofReal_ne_top
    change (ballVolume g p r / C) / (D / C) = ballVolume g p r / D
    apply (ENNReal.div_eq_div_iff hD0 hDt
      (ENNReal.div_pos hD0 hCt).ne' (ENNReal.div_ne_top hDt hC0)).2
    simp only [div_eq_mul_inv]
    ac_rfl
  exact hdiv.congr' heq

end Poincare.Geometry.Riemannian.VolumeComparison
