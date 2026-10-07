import DifferentialGeometry.Geometry.Hyperbolic.TruncationDistance
import DifferentialGeometry.Geometry.Measure.PartialDiffeomorphBalls
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set Filter Manifold MeasureTheory GC.Endpoint
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

private theorem le_log_div_of_le_mul_exp_neg {A w s : ℝ}
    (hA : 0 < A) (hw : 0 < w) (h : w ≤ A * Real.exp (-s)) :
    s ≤ Real.log (A / w) := by
  have hdiv : w / A ≤ Real.exp (-s) := by
    apply (div_le_iff₀ hA).mpr
    simpa only [mul_comm] using h
  have hlog := (Real.log_le_iff_le_exp (div_pos hw hA)).mpr hdiv
  rw [Real.log_div hw.ne' hA.ne'] at hlog
  rw [Real.log_div hA.ne' hw.ne']
  linarith

private theorem exists_pos_log_inv_lt_reciprocal (C₀ C₁ c : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∀ w : ℝ, 0 < w → w < δ →
      C₀ + C₁ * Real.log (1 / w) < c / w := by
  have hlog : Tendsto (fun w : ℝ => w * Real.log (1 / w)) (𝓝[>] 0) (𝓝 0) := by
    have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_inv_nhdsGT_zero : Tendsto (fun w : ℝ => w⁻¹) (𝓝[>] 0) atTop)
    change Tendsto (fun w : ℝ => Real.log w⁻¹ / w⁻¹) (𝓝[>] 0) (𝓝 0) at h
    simpa only [one_div, div_inv_eq_mul, mul_comm] using h
  have hid : Tendsto (fun w : ℝ => w) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsum : Tendsto (fun w : ℝ => w * C₀ + (w * Real.log (1 / w)) * C₁)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul, add_zero] using (hid.mul_const C₀).add (hlog.mul_const C₁)
  have htotal : Tendsto (fun w : ℝ => w * (C₀ + C₁ * Real.log (1 / w)))
      (𝓝[>] 0) (𝓝 0) := by
    convert hsum using 1
    funext w
    ring
  have hevent : ∀ᶠ w : ℝ in 𝓝[>] 0,
      w * (C₀ + C₁ * Real.log (1 / w)) < c :=
    htotal.eventually_lt_const hc
  obtain ⟨δ, hδ, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  refine ⟨δ, hδ, ?_⟩
  intro w hw hwδ
  apply (lt_div_iff₀ hw).mpr
  have hh := hbound ⟨hw, hwδ⟩
  change w * (C₀ + C₁ * Real.log (1 / w)) < c at hh
  simpa only [mul_comm] using hh

universe u

theorem exists_log_radius_volume_superlevel_subset_ball_of_radius_pos
    {H : FiniteVolumeHyperbolicModel.{u}} (Tr : HyperbolicTruncation H) (o : H.Carrier)
    {R : ℝ} (hR : 0 < R) :
    ∃ C > 0, ∀ w : ℝ, 0 < w → w ≤ 1 →
      {y : H.Carrier | ENNReal.ofReal (w * R ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
          (riemannianBallOf H.metric y R)} ⊆
        riemannianBallOf H.metric o (C + Real.log (1 / w)) := by
  let μ := Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
  let V : ℝ≥0∞ := μ univ
  have hV : V ≠ ⊤ := H.finite_volume.ne
  have harea (i : Fin Tr.count) :
      Integral.Measure.riemannianVolumeMeasure torusModel Torus
        (Tr.cusp i).torusMetric univ ≤ V := by
    have htail := Tr.volume_image_cusp_tail i (by norm_num : (0 : ℝ) ≤ 0)
    simp only [neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one] at htail
    rw [← htail]
    exact measure_mono (subset_univ _)
  let A : ℝ := max 1 (V.toReal * Real.exp R / R ^ 3)
  have hAone : 1 ≤ A := le_max_left _ _
  have hA : 0 < A := zero_lt_one.trans_le hAone
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hAone
  obtain ⟨D, hD, hcore, hcusp⟩ := Tr.exists_core_and_cusp_distance_bound o
  let C : ℝ := D + R + 1 + Real.log A
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro w hw hw1 y hy
  have hlogw : 0 ≤ Real.log (1 / w) := Real.log_nonneg ((one_le_div hw).mpr hw1)
  have hCw : 0 < C + Real.log (1 / w) := add_pos_of_pos_of_nonneg hC hlogw
  have hycover : y ∈ range Tr.inclusion ∪ ⋃ i, range (Tr.cuspMap i) := by
    rw [Tr.exhausts]
    exact mem_univ y
  rcases hycover with ⟨q, rfl⟩ | hycusp
  · apply (hcore q).trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff hCw).mpr
    dsimp [C]
    linarith
  · obtain ⟨i, p, rfl⟩ := mem_iUnion.mp hycusp
    apply (hcusp i p).trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff hCw).mpr
    by_cases hs : p.2.val 0 ≤ R
    · dsimp [C]
      linarith
    · have hsR : R < p.2.val 0 := lt_of_not_ge hs
      have hupper := Tr.volume_riemannianBallOf_cuspMap_le i p hR hsR
      have htotal : μ (riemannianBallOf H.metric (Tr.cuspMap i p) R) ≤
          V * ENNReal.ofReal (Real.exp (R - p.2.val 0)) :=
        hupper.trans (mul_le_mul_left (harea i) _)
      have hmass : ENNReal.ofReal (w * R ^ 3) ≤
          V * ENNReal.ofReal (Real.exp (R - p.2.val 0)) := hy.trans htotal
      rw [← ENNReal.ofReal_toReal hV, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at hmass
      have hreal : w * R ^ 3 ≤ V.toReal * Real.exp (R - p.2.val 0) :=
        (ENNReal.ofReal_le_ofReal_iff
          (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)).mp hmass
      have hexp : Real.exp (R - p.2.val 0) = Real.exp R * Real.exp (-p.2.val 0) := by
        rw [sub_eq_add_neg, Real.exp_add]
      rw [hexp] at hreal
      have hwexp : w ≤ A * Real.exp (-p.2.val 0) := by
        have hscale : w ≤ (V.toReal * Real.exp R / R ^ 3) * Real.exp (-p.2.val 0) := by
          calc
            w ≤ (V.toReal * Real.exp R * Real.exp (-p.2.val 0)) / R ^ 3 := by
              apply (le_div_iff₀ (pow_pos hR 3)).mpr
              simpa only [mul_assoc] using hreal
            _ = (V.toReal * Real.exp R / R ^ 3) * Real.exp (-p.2.val 0) := by ring
        exact hscale.trans (mul_le_mul_of_nonneg_right
          (le_max_right 1 (V.toReal * Real.exp R / R ^ 3)) (Real.exp_pos _).le)
      have hslog : p.2.val 0 ≤ Real.log A + Real.log (1 / w) := by
        have h := le_log_div_of_le_mul_exp_neg hA hw hwexp
        simpa only [Real.log_div hA.ne' hw.ne', one_div, Real.log_inv,
          sub_eq_add_neg] using h
      dsimp [C]
      linarith

theorem exists_log_radius_volume_superlevel_subset_ball
    {H : FiniteVolumeHyperbolicModel.{u}} (Tr : HyperbolicTruncation H) (o : H.Carrier) :
    ∃ C > 0, ∀ w : ℝ, 0 < w → w ≤ 1 →
      {y : H.Carrier | ENNReal.ofReal (8 * w) ≤
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
          (riemannianBallOf H.metric y 2)} ⊆
        riemannianBallOf H.metric o (C + Real.log (1 / w)) := by
  simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num, mul_comm] using
    Tr.exists_log_radius_volume_superlevel_subset_ball_of_radius_pos o
      (by norm_num : (0 : ℝ) < 2)

theorem exists_inv_radius_volume_superlevel_subset_ball_of_radius_pos
    {H : FiniteVolumeHyperbolicModel.{u}} (Tr : HyperbolicTruncation H) (o : H.Carrier)
    {R : ℝ} (hR : 0 < R) (c : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∀ w : ℝ, 0 < w → w < δ →
      {y : H.Carrier | ENNReal.ofReal (w * R ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
          (riemannianBallOf H.metric y R)} ⊆
        riemannianBallOf H.metric o (c / w) := by
  obtain ⟨C, _, hC⟩ := exists_log_radius_volume_superlevel_subset_ball_of_radius_pos Tr o hR
  obtain ⟨δ, hδ, hδbound⟩ := exists_pos_log_inv_lt_reciprocal C 1 c hc
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro w hw hwδ y hy
  have hw1 : w ≤ 1 := (hwδ.trans_le (min_le_right δ 1)).le
  have hsmall : C + Real.log (1 / w) < c / w := by
    simpa only [one_mul] using hδbound w hw (hwδ.trans_le (min_le_left δ 1))
  exact riemannianBallOf_mono H.metric o hsmall.le (hC w hw hw1 hy)

theorem exists_inv_radius_volume_superlevel_subset_ball
    {H : FiniteVolumeHyperbolicModel.{u}} (Tr : HyperbolicTruncation H) (o : H.Carrier)
    (c : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∀ w : ℝ, 0 < w → w < δ →
      {y : H.Carrier | ENNReal.ofReal (8 * w) ≤
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
          (riemannianBallOf H.metric y 2)} ⊆
        riemannianBallOf H.metric o (c / w) := by
  simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num, mul_comm] using
    Tr.exists_inv_radius_volume_superlevel_subset_ball_of_radius_pos o
      (by norm_num : (0 : ℝ) < 2) c hc

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

universe u v w z

theorem exists_metric_tolerance_volume_superlevel_preimage_subset_ball
    {H : FiniteVolumeHyperbolicModel.{u}} (Tr : HyperbolicTruncation H) (o : H.Carrier) :
    ∃ η > 0, ∃ δ > 0, ∀ w : ℝ, 0 < w → w < η →
      ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
        [FiniteDimensional ℝ F] (H' : Type w) [TopologicalSpace H']
        (J : ModelWithCorners ℝ F H') [J.Boundaryless]
        (N : Type z) [TopologicalSpace N] [ChartedSpace H' N]
        [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
        (h : SmoothRiemannianMetric J N)
        (Φ : PartialDiffeomorph (𝓡 3) J H.Carrier N ∞) (p : H.Carrier),
        ∀ a b s R : ℝ, |a - 1| < δ → |b - 1| < δ → |s - 2| < δ →
        s / a < R → b * s < R →
        riemannianClosedBallOf H.metric p R ⊆ Φ.source →
        (∀ x ∈ riemannianClosedBallOf H.metric p R, ∀ v : TangentSpace (𝓡 3) x,
          H.metric.inner x v v ≤ b ^ 2 * h.inner (Φ x)
            (mfderiv (𝓡 3) J (Φ : H.Carrier → N) x v)
            (mfderiv (𝓡 3) J (Φ : H.Carrier → N) x v)) →
        (∀ x ∈ riemannianClosedBallOf H.metric p R, ∀ v : TangentSpace (𝓡 3) x,
          h.inner (Φ x) (mfderiv (𝓡 3) J (Φ : H.Carrier → N) x v)
            (mfderiv (𝓡 3) J (Φ : H.Carrier → N) x v) ≤
              a ^ 2 * H.metric.inner x v v) →
        ENNReal.ofReal (w * s ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure J N h (riemannianBallOf h (Φ p) s) →
        p ∈ riemannianBallOf H.metric o (1 / (2 * w)) := by
  obtain ⟨τ, hτ, hloc⟩ :=
    Tr.exists_inv_radius_volume_superlevel_subset_ball_of_radius_pos o
      (by norm_num : (0 : ℝ) < 3) (1 / 432) (by norm_num)
  refine ⟨216 * τ, by positivity, (1 / 16 : ℝ), by norm_num, ?_⟩
  intro w hw hwη F _ _ _ H' _ J _ N _ _ _ _ _ h Φ p a b s R ha hb hs hsmall hlarge
    hsource hlower hupper hmass
  have hapos : 0 < a := by
    have := (abs_lt.mp ha).1
    linarith
  have ha2 : a ≤ 2 := by
    have := (abs_lt.mp ha).2
    linarith
  have hbpos : 0 < b := by
    have := (abs_lt.mp hb).1
    linarith
  have hbupper : b ≤ 17 / 16 := by
    have := (abs_lt.mp hb).2
    linarith
  have hsone : 1 ≤ s := by
    have := (abs_lt.mp hs).1
    linarith
  have hspos : 0 < s := zero_lt_one.trans_le hsone
  have hsupper : s ≤ 33 / 16 := by
    have := (abs_lt.mp hs).2
    linarith
  have hlarge3 : b * s ≤ 3 := by
    calc
      b * s ≤ (17 / 16 : ℝ) * (33 / 16) :=
        mul_le_mul hbupper hsupper hspos.le (by norm_num)
      _ ≤ 3 := by norm_num
  let _ : IsManifold (𝓡 3) 1 H.Carrier :=
    IsManifold.of_le (I := 𝓡 3) (n := ∞) (by decide)
  have hcpt : IsCompact (riemannianClosedBallOf H.metric p R) :=
    H.complete.closedEBall_isCompact p R
  have hhi := (Geometry.Measure.riemannianVolumeMeasure_ball_bounds_of_partialDiffeomorph_metric_bounds
    H.metric h Φ p hapos hbpos hsmall hlarge hcpt hsource hlower hupper).2
  have hpow : a ^ 3 ≤ (8 : ℝ) := by
    calc
      a ^ 3 ≤ (2 : ℝ) ^ 3 := pow_le_pow_left₀ hapos.le ha2 _
      _ = 8 := by norm_num
  have hmass8 : ENNReal.ofReal (w * s ^ 3) ≤ ENNReal.ofReal 8 *
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
        (riemannianBallOf H.metric p 3) := by
    apply hmass.trans
    apply hhi.trans
    apply mul_le_mul'
    · simpa only [finrank_euclideanSpace_fin] using ENNReal.ofReal_le_ofReal hpow
    · exact measure_mono (riemannianBallOf_mono H.metric p hlarge3)
  have hfinite : Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
      (riemannianBallOf H.metric p 3) ≠ ⊤ :=
    ne_top_of_le_ne_top H.finite_volume.ne (measure_mono (subset_univ _))
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) hmass8
  rw [ENNReal.toReal_ofReal (mul_nonneg hw.le (pow_nonneg hspos.le _)),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 8)] at hreal
  have hmass3 : ENNReal.ofReal ((w / 216) * (3 : ℝ) ^ 3) ≤
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
        (riemannianBallOf H.metric p 3) := by
    rw [← ENNReal.ofReal_toReal hfinite]
    apply ENNReal.ofReal_le_ofReal
    have hs3 : (1 : ℝ) ≤ s ^ 3 := one_le_pow₀ hsone
    have hws := mul_le_mul_of_nonneg_left hs3 hw.le
    nlinarith
  have hmatch := hloc (w / 216) (by positivity) (by linarith) hmass3
  have hradius : (1 / 432 : ℝ) / (w / 216) = 1 / (2 * w) := by
    field_simp
    norm_num
  simpa only [hradius] using hmatch

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
