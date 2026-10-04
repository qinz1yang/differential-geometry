import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromov
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling

/-!
# Three-dimensional local volume comparison from sectional curvature

The metric, distance, complete-space and boundaryless instances are retained explicitly.
The sectional and Ricci conventions are those of the inherited comparison library.
The two Riemannian ball-volume definitions are identified through metric compatibility.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

section Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem ricciBoundedBelowOn_of_sectional_three
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    {S : Set M} {K : ℝ}
    (hsec : ∀ q ∈ S, SectionalBoundedBelowAt g q K) :
    ricciBoundedBelowOn g S (2 * K) := by
  intro q hq v
  simpa only [hdim, Nat.reduceSub, Nat.cast_ofNat] using
    ricci_lower_of_sectionalBoundedBelowAt g q (hsec q hq) v

end Curvature

section Comparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
theorem collapseBallVolume_eq_comparison
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) (r : ℝ) :
    Collapse.ballVolume g p r = ballVolume g p r := by
  unfold Collapse.ballVolume ballVolume riemannianBallOf
  simp only [riemannianEDistOf_eq_riemannianEDist g hEnorm]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
theorem sectionalThree_ballVolume_mono
    (g : SmoothRiemannianMetric I M) (p : M) : Monotone (ballVolume g p) := by
  intro r R hrR
  apply measure_mono
  intro q hq
  exact hq.trans_le (ENNReal.ofReal_le_ofReal hrR)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
theorem sectionalThree_ballVolume_pos
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ} (hr : 0 < r) :
    0 < ballVolume g p r := by
  let : (riemannianVolumeMeasure (I := I) (M := M) g).IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure g
  exact Measure.measure_pos_of_mem_nhds
    (riemannianVolumeMeasure (I := I) (M := M) g)
    (eventually_riemannianEDist_lt I p (ENNReal.ofReal_pos.mpr hr))

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
theorem sectionalThree_ricci_on_ball
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hdim : Module.finrank ℝ E = 3) (p : M) {K R : ℝ}
    (hsec : ∀ q ∈ riemannianBallOf g p R, SectionalBoundedBelowAt g q K) :
    ricciBoundedBelowOn g
      {q : M | riemannianEDist I p q < ENNReal.ofReal R} (2 * K) := by
  apply ricciBoundedBelowOn_of_sectional_three g hdim
  intro q hq
  apply hsec q
  simpa only [riemannianBallOf, mem_ofPred_eq,
    riemannianEDistOf_eq_riemannianEDist g hEnorm] using hq

variable [ConnectedSpace M] [CompleteSpace M]

theorem sectionalThree_ballVolume_finite_of_complete
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) {r : ℝ} (hr : 0 < r) : ballVolume g p r < ⊤ := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let : IsLocallyFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure g
  let : FiniteDimensional ℝ (TangentSpace I p) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let : ProperSpace (TangentSpace I p) := FiniteDimensional.proper_real _
  let f := Exponential.expMapIntrinsic (I := I) g hEnorm p
  have hcompact : IsCompact (f '' Metric.closedBall (0 : TangentSpace I p) r) :=
    (isCompact_closedBall (0 : TangentSpace I p) r).image
      (Exponential.expMapIntrinsic_continuous g hEnorm p)
  have hsubset : {q : M | riemannianEDist I p q < ENNReal.ofReal r} ⊆
      f '' Metric.closedBall (0 : TangentSpace I p) r := by
    intro q hq
    obtain ⟨v, hv, hlen⟩ :=
      Exponential.hopf_rinow_expMapIntrinsic_surjective_minimizing g hEnorm p q
    refine ⟨v, ?_, hv⟩
    have hnorm : ‖v‖ = Real.sqrt (g.inner p v v) := by
      have henorm := hEnorm p v
      rw [← ofReal_norm] at henorm
      exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v)
        (Real.sqrt_nonneg _)).mp henorm
    rw [Metric.mem_closedBall, dist_zero_right, hnorm, hlen]
    have hfin : riemannianEDist I p q ≠ ⊤ :=
      ne_top_of_lt (hq.trans ENNReal.ofReal_lt_top)
    have hreal := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hq
    exact (by simpa only [ENNReal.toReal_ofReal hr.le] using hreal.le)
  have hfinite : riemannianVolumeMeasure (I := I) (M := M) g
      (f '' Metric.closedBall (0 : TangentSpace I p) r) < ⊤ := hcompact.measure_lt_top
  exact (measure_mono hsubset).trans_lt hfinite

theorem localBishopGromov_cross_sectional_three
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hdim : Module.finrank ℝ E = 3) (p : M) {κ s R R₀ : ℝ}
    (hκ : 0 ≤ κ) (hs : 0 < s) (hsR : s ≤ R) (hRR₀ : R < R₀)
    (hsec : ∀ q ∈ riemannianBallOf g p R₀, SectionalBoundedBelowAt g q (-κ)) :
    ballVolume g p R * ENNReal.ofReal (modelVolume (-κ) 3 s) ≤
      ENNReal.ofReal (modelVolume (-κ) 3 R) * ballVolume g p s := by
  have hRic := sectionalThree_ricci_on_ball g hEnorm hdim p hsec
  have hconj : 0 < -κ → R < Real.pi / Real.sqrt (-κ) := by
    intro hpos
    exact (not_lt_of_ge (neg_nonpos.mpr hκ) hpos).elim
  have hRic' : ricciBoundedBelowOn g
      {q : M | riemannianEDist I p q < ENNReal.ofReal R₀}
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-κ)) := by
    simpa only [hdim, Nat.reduceSub, Nat.cast_ofNat] using hRic
  simpa only [ballVolume, hdim] using
    modelVolume_cross_of_ricciBoundedBelowOn g hEnorm p hs hsR hconj hRR₀ hRic'

theorem localBishopGromov_cross_endpoint_sectional_three
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hdim : Module.finrank ℝ E = 3) (p : M) {κ s R : ℝ}
    (hκ : 0 ≤ κ) (hs : 0 < s) (hsR : s ≤ R)
    (hsec : ∀ q ∈ riemannianBallOf g p R, SectionalBoundedBelowAt g q (-κ)) :
    ballVolume g p R * ENNReal.ofReal (modelVolume (-κ) 3 s) ≤
      ENNReal.ofReal (modelVolume (-κ) 3 R) * ballVolume g p s := by
  have hRic := sectionalThree_ricci_on_ball g hEnorm hdim p hsec
  have hconj : 0 < -κ → R ≤ Real.pi / Real.sqrt (-κ) := by
    intro hpos
    exact (not_lt_of_ge (neg_nonpos.mpr hκ) hpos).elim
  have hRic' : ricciBoundedBelowOn g
      {q : M | riemannianEDist I p q < ENNReal.ofReal R}
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-κ)) := by
    simpa only [hdim, Nat.reduceSub, Nat.cast_ofNat] using hRic
  simpa only [ballVolume, hdim] using
    modelVolume_cross_endpoint_of_ricciBoundedBelowOn g hEnorm p hs hsR hconj hRic'

theorem localBishopGromov_upper_sectional_three
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hdim : Module.finrank ℝ E = 3) (p : M) {κ R : ℝ}
    (hκ : 0 ≤ κ) (hR : 0 < R)
    (hsec : ∀ q ∈ riemannianBallOf g p R, SectionalBoundedBelowAt g q (-κ)) :
    ballVolume g p R ≤ ENNReal.ofReal (modelVolume (-κ) 3 R) := by
  have hRic := sectionalThree_ricci_on_ball g hEnorm hdim p hsec
  let R₀ : Set.Ioi (0 : ℝ≥0∞) := ⟨ENNReal.ofReal R, ENNReal.ofReal_pos.mpr hR⟩
  have hRic' : ricciBoundedBelowOn g
      {q : M | riemannianEDist I p q < R₀.1}
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-κ)) := by
    simpa only [R₀, hdim, Nat.reduceSub, Nat.cast_ofNat] using hRic
  have hbound : ENNReal.ofReal R ≤ bishopGromovRadius (-κ) R₀.1 := by
    rw [bishopGromovRadius_of_nonpos (neg_nonpos.mpr hκ)]
  simpa only [hdim] using
    localBishopGromov_absolute_upper g hEnorm p (-κ) R₀ hRic' hR hbound

theorem sectionalThree_ballVolume_pos_finite
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hdim : Module.finrank ℝ E = 3) (p : M) {κ s R : ℝ}
    (hκ : 0 ≤ κ) (hs : 0 < s) (hsR : s ≤ R)
    (hsec : ∀ q ∈ riemannianBallOf g p R, SectionalBoundedBelowAt g q (-κ)) :
    0 < ballVolume g p s ∧ ballVolume g p s < ⊤ := by
  refine ⟨sectionalThree_ballVolume_pos g p hs, ?_⟩
  exact ((sectionalThree_ballVolume_mono g p hsR).trans
    (localBishopGromov_upper_sectional_three g hEnorm hdim p hκ
      (hs.trans_le hsR) hsec)).trans_lt ENNReal.ofReal_lt_top

theorem localBishopGromov_real_cross_sectional_three
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hdim : Module.finrank ℝ E = 3) (p : M) {κ s R : ℝ}
    (hκ : 0 ≤ κ) (hs : 0 < s) (hsR : s ≤ R)
    (hsec : ∀ q ∈ riemannianBallOf g p R, SectionalBoundedBelowAt g q (-κ)) :
    (ballVolume g p R).toReal * modelVolume (-κ) 3 s ≤
      modelVolume (-κ) 3 R * (ballVolume g p s).toReal := by
  have hfinite := sectionalThree_ballVolume_pos_finite g hEnorm hdim p hκ hs hsR hsec
  have hm (r : ℝ) (hr : 0 < r) : 0 < modelVolume (-κ) 3 r :=
    modelVolume_pos (by norm_num) hr
      ⟨hr.le, fun hpos => (not_lt_of_ge (neg_nonpos.mpr hκ) hpos).elim⟩
  have hcross := localBishopGromov_cross_endpoint_sectional_three
    g hEnorm hdim p hκ hs hsR hsec
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite.2.ne) hcross
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hm s hs).le,
    ENNReal.toReal_ofReal (hm R (hs.trans_le hsR)).le] using hreal

theorem localBishopGromov_relative_ratios_sectional_three
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hdim : Module.finrank ℝ E = 3) (p : M) {κ s R : ℝ}
    (hκ : 0 ≤ κ) (hs : 0 < s) (hsR : s ≤ R)
    (hsec : ∀ q ∈ riemannianBallOf g p R, SectionalBoundedBelowAt g q (-κ)) :
    0 < (ballVolume g p s).toReal ∧ 0 < (ballVolume g p R).toReal ∧
      ballVolume g p s < ⊤ ∧ ballVolume g p R < ⊤ ∧
      (ballVolume g p R).toReal / (ballVolume g p s).toReal ≤
        modelVolume (-κ) 3 R / modelVolume (-κ) 3 s ∧
      modelVolume (-κ) 3 s / modelVolume (-κ) 3 R ≤
        (ballVolume g p s).toReal / (ballVolume g p R).toReal := by
  have hsvol := sectionalThree_ballVolume_pos_finite g hEnorm hdim p hκ hs hsR hsec
  have hRvol := sectionalThree_ballVolume_pos_finite g hEnorm hdim p hκ
    (hs.trans_le hsR) le_rfl hsec
  have hsreal := ENNReal.toReal_pos hsvol.1.ne' hsvol.2.ne
  have hRreal := ENNReal.toReal_pos hRvol.1.ne' hRvol.2.ne
  have hm (r : ℝ) (hr : 0 < r) : 0 < modelVolume (-κ) 3 r :=
    modelVolume_pos (by norm_num) hr
      ⟨hr.le, fun hpos => (not_lt_of_ge (neg_nonpos.mpr hκ) hpos).elim⟩
  have hcross := localBishopGromov_real_cross_sectional_three
    g hEnorm hdim p hκ hs hsR hsec
  refine ⟨hsreal, hRreal, hsvol.2, hRvol.2, ?_, ?_⟩
  · exact (div_le_div_iff₀ hsreal (hm s hs)).mpr hcross
  · apply (div_le_div_iff₀ (hm R (hs.trans_le hsR)) hRreal).mpr
    simpa only [mul_comm] using hcross

theorem sectionalThree_euclidean_le_model {κ r : ℝ} (hκ : 0 ≤ κ) (hr : 0 ≤ r) :
    euclideanUnitBallVolume 3 * r ^ 3 ≤ modelVolume (-κ) 3 r := by
  rw [← modelVolume_zero 3 r (by norm_num)]
  apply intervalIntegral.integral_mono_on_of_le_Ioo hr
    ((modelArea_continuous 0 3).intervalIntegrable 0 r)
    ((modelArea_continuous (-κ) 3).intervalIntegrable 0 r)
  intro t ht
  have hrad : t ≤ modelRadius (-κ) t := by
    rw [modelRadius_eq_hypSn_of_nonpos (-κ) t (neg_nonpos.mpr hκ)]
    let q := Real.sqrt (-(-κ))
    change t ≤ hyperbolicSn q t
    by_cases hq : q = 0
    · simp only [hyperbolicSn, hq, ite_true, le_refl]
    · have hqpos : 0 < q := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hq)
      rw [hyperbolicSn, ite_eq_right hq, le_div_iff₀ hqpos]
      simpa only [mul_comm] using
        (Real.self_le_sinh_iff.mpr (mul_nonneg hqpos.le ht.1.le))
  simp only [modelArea, modelRadius_zero]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1.le hrad 2)
    (mul_nonneg (by norm_num) (euclideanUnitBallVolume_pos 3).le)

theorem sectionalThree_model_at_inverse_radius {R : ℝ} (hR : 0 < R) :
    modelVolume (-(R ^ 2)⁻¹) 3 R = R ^ 3 * modelVolume (-1) 3 1 := by
  have h := modelVolume_neg_sq_scale 1 R 1 3 zero_le_one hR (by norm_num)
  simpa only [one_div, one_pow, mul_one, inv_pow] using h

theorem sectionalThree_model_hyperbolic_integral (r : ℝ) :
    modelVolume (-1) 3 r =
      3 * euclideanUnitBallVolume 3 * (∫ t in (0 : ℝ)..r, Real.sinh t ^ 2) := by
  have h := modelVolume_neg_sq 1 3 r zero_le_one
  simpa only [one_pow, Nat.cast_ofNat, Nat.reduceSub, hyperbolicRadialVolume,
    hyperbolicDensity, hyperbolicSn, one_ne_zero, ite_false, one_mul, div_one] using h

theorem sectionalThree_hyperbolic_integral_pos :
    0 < ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2 := by
  have hm : 0 < modelVolume (-1) 3 1 :=
    modelVolume_pos (by norm_num) zero_lt_one ⟨zero_le_one, by norm_num⟩
  rw [sectionalThree_model_hyperbolic_integral] at hm
  exact (mul_pos_iff_of_pos_left
    (mul_pos (by norm_num) (euclideanUnitBallVolume_pos 3))).mp hm

theorem sectionalThree_volume_upper_at_modified_scale
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hdim : Module.finrank ℝ E = 3) (p : M) {w r ρ : ℝ}
    (hw : 0 < w) (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r ≤ 2 * ρ)
    (hvol : Collapse.ballVolume g p r = ENNReal.ofReal (w * r ^ 3))
    (hsec : ∀ q ∈ riemannianBallOf g p (2 * ρ),
      SectionalBoundedBelowAt g q (-((2 * ρ) ^ 2)⁻¹)) :
    (Collapse.ballVolume g p (2 * ρ)).toReal / (2 * ρ) ^ 3 ≤
      (3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) * w := by
  rw [collapseBallVolume_eq_comparison g hEnorm] at hvol ⊢
  have hR : 0 < 2 * ρ := mul_pos (by norm_num) hρ
  have hκ : 0 ≤ ((2 * ρ) ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  have hcross := localBishopGromov_real_cross_sectional_three
    g hEnorm hdim p hκ hr hrρ hsec
  rw [hvol, ENNReal.toReal_ofReal (mul_pos hw (pow_pos hr 3)).le,
    sectionalThree_model_at_inverse_radius hR] at hcross
  have hmodel := sectionalThree_euclidean_le_model hκ hr.le
  have hstep :
      ((ballVolume g p (2 * ρ)).toReal * euclideanUnitBallVolume 3) * r ^ 3 ≤
        ((2 * ρ) ^ 3 * modelVolume (-1) 3 1 * w) * r ^ 3 := by
    calc
      _ = (ballVolume g p (2 * ρ)).toReal *
          (euclideanUnitBallVolume 3 * r ^ 3) := by ring
      _ ≤ (ballVolume g p (2 * ρ)).toReal *
          modelVolume (-((2 * ρ) ^ 2)⁻¹) 3 r :=
        mul_le_mul_of_nonneg_left hmodel ENNReal.toReal_nonneg
      _ ≤ _ := by nlinarith only [hcross]
  have hcancel := (mul_le_mul_iff_left₀ (pow_pos hr 3)).mp hstep
  rw [sectionalThree_model_hyperbolic_integral] at hcancel
  apply (div_le_iff₀ (pow_pos hR 3)).mpr
  apply (mul_le_mul_iff_left₀ (euclideanUnitBallVolume_pos 3)).mp
  nlinarith only [hcancel]

theorem sectionalThree_volume_lower_at_modified_scale
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hdim : Module.finrank ℝ E = 3) (p : M) {w u ρ : ℝ}
    (hw : 0 < w) (hu : 0 < u) (hρ : 0 < ρ) (hρu : ρ ≤ 2 * u)
    (hvol : Collapse.ballVolume g p u = ENNReal.ofReal (w * u ^ 3))
    (hsec : ∀ q ∈ riemannianBallOf g p u,
      SectionalBoundedBelowAt g q (-(u ^ 2)⁻¹)) :
    0 < w / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ∧
      w / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤
        (Collapse.ballVolume g p ρ).toReal / ρ ^ 3 := by
  rw [collapseBallVolume_eq_comparison g hEnorm] at hvol ⊢
  have hI := sectionalThree_hyperbolic_integral_pos
  have hs : 0 < ρ / 2 := half_pos hρ
  have hsu : ρ / 2 ≤ u := by linarith
  have hκ : 0 ≤ (u ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  have hcross := localBishopGromov_real_cross_sectional_three
    g hEnorm hdim p hκ hs hsu hsec
  rw [hvol, ENNReal.toReal_ofReal (mul_pos hw (pow_pos hu 3)).le,
    sectionalThree_model_at_inverse_radius hu] at hcross
  have hmodel := sectionalThree_euclidean_le_model hκ hs.le
  have hmono : (ballVolume g p (ρ / 2)).toReal ≤ (ballVolume g p ρ).toReal :=
    ENNReal.toReal_mono (sectionalThree_ballVolume_finite_of_complete
      g hEnorm p hρ).ne (sectionalThree_ballVolume_mono g p (by linarith))
  have hM : 0 < modelVolume (-1) 3 1 :=
    modelVolume_pos (by norm_num) zero_lt_one ⟨zero_le_one, by norm_num⟩
  have hstep :
      u ^ 3 * (w * euclideanUnitBallVolume 3 * (ρ / 2) ^ 3) ≤
        u ^ 3 * (modelVolume (-1) 3 1 * (ballVolume g p ρ).toReal) := by
    calc
      _ = (w * u ^ 3) * (euclideanUnitBallVolume 3 * (ρ / 2) ^ 3) := by ring
      _ ≤ (w * u ^ 3) * modelVolume (-(u ^ 2)⁻¹) 3 (ρ / 2) :=
        mul_le_mul_of_nonneg_left hmodel (mul_pos hw (pow_pos hu 3)).le
      _ ≤ (u ^ 3 * modelVolume (-1) 3 1) * (ballVolume g p (ρ / 2)).toReal :=
        hcross
      _ ≤ _ := by
        nlinarith only [mul_le_mul_of_nonneg_left hmono (mul_pos (pow_pos hu 3) hM).le]
  have hcancel := (mul_le_mul_iff_right₀ (pow_pos hu 3)).mp hstep
  rw [sectionalThree_model_hyperbolic_integral] at hcancel
  refine ⟨div_pos hw (mul_pos (by norm_num) hI), ?_⟩
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hI) (pow_pos hρ 3)).mpr
  apply (mul_le_mul_iff_left₀ (euclideanUnitBallVolume_pos 3)).mp
  nlinarith only [hcancel]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M)]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [ConnectedSpace M] [CompleteSpace M] in
theorem sectionalThree_rescaled_ballVolume
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    (p : M) {ρ : ℝ} (hρ : 0 < ρ) :
    (Collapse.ballVolume (scaleMetric (ρ ^ 2)⁻¹ (inv_pos.mpr (sq_pos_of_pos hρ)) g)
      p 2).toReal = (Collapse.ballVolume g p (2 * ρ)).toReal / ρ ^ 3 := by
  have hsqrt : Real.sqrt ((ρ ^ 2)⁻¹) = ρ⁻¹ := by
    rw [Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos hρ]
  have harg : Real.sqrt ((ρ ^ 2)⁻¹) * (2 * ρ) = 2 := by
    rw [hsqrt]
    field_simp
  have hball := riemannianBallOf_scaleMetric
    (ρ ^ 2)⁻¹ (inv_pos.mpr (sq_pos_of_pos hρ)) g p (2 * ρ)
  rw [harg] at hball
  unfold Collapse.ballVolume
  rw [hball, volume_scale_apply, hdim, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), hsqrt]
  simp only [div_eq_mul_inv, inv_pow, mul_comm]

theorem sectionalThree_scaled_volume_upper_at_modified_scale
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hdim : Module.finrank ℝ E = 3) (p : M) {w r ρ : ℝ}
    (hw : 0 < w) (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r ≤ 2 * ρ)
    (hvol : Collapse.ballVolume g p r = ENNReal.ofReal (w * r ^ 3))
    (hsec : ∀ q ∈ riemannianBallOf g p (2 * ρ),
      SectionalBoundedBelowAt g q (-((2 * ρ) ^ 2)⁻¹)) :
    (Collapse.ballVolume (scaleMetric (ρ ^ 2)⁻¹ (inv_pos.mpr (sq_pos_of_pos hρ)) g)
      p 2).toReal ≤ 8 * (3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) * w := by
  have hbound := sectionalThree_volume_upper_at_modified_scale
    g hEnorm hdim p hw hr hρ hrρ hvol hsec
  rw [sectionalThree_rescaled_ballVolume g hdim p hρ]
  apply (div_le_iff₀ (pow_pos hρ 3)).mpr
  have hR : 0 < 2 * ρ := mul_pos (by norm_num) hρ
  have hmul := (div_le_iff₀ (pow_pos hR 3)).mp hbound
  nlinarith only [hmul]

end Comparison

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
