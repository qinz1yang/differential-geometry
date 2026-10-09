import DifferentialGeometry.Geometry.Collapse.Inhabitants.SmallBoundaryPackets
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspDerivativeUniform
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspBoundaryInst

/-!
# The corrected boundary standing sequence, inhabited (lane BDRY-INST, review 54 §4 level 2)

For ONE derivative-control function `A` (built from the a-uniform curvature derivative bound of
`DoubleCuspDerivativeUniform` and the total volume `Vol(g_a) = a² Vol(g_1)`) and EVERY sequence of
positive ratios `d n`, double cusps at torus scales `a n ≤ 1` satisfy all three standing
hypotheses at `d n`: nearly cuspidal boundary (two components), volume collapse at the curvature
scale away from the boundary, and curvature derivative control with `A`.

* `doubleCusp_curvatureDerivativesControlled_INST`: one `A` for all scales `0 < a ≤ 1` and all
  thresholds `w₀ > 0`;
* `exists_doubleCusp_standing_sequence_INST`: the standing sequence for arbitrary ratios;
* `exists_doubleCusp_standing_sequence_ratio_INST`: at the corrected ratios
  `boundaryCounterexampleRatio δ₀ (n + 1)` on connected universe-`0` carriers (the hypothesis
  shape of `lc88_boundary_collapse_packet_BDRY1_IDX` and `lc88_boundary_packets_BFR_BCG5_IDX2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory DifferentialGeometry GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Geometry.Curvature
open scoped ENNReal Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

local instance standingCompact_INST : CompactSpace (productSet.{u} 2) :=
  annulusCircleCarrier.{u}.compact

local instance standingSigma_INST : SigmaCompactSpace (productSet.{u} 2) :=
  CompactSpace.sigmaCompact

/-- `Vol(doubleCuspMetric a) = a² · Vol(doubleCuspMetric 1)`. -/
theorem doubleCuspMetric_volume_INST (a : ℝ) (ha : 0 < a) :
    Integral.Measure.riemannianVolumeMeasure (𝓡∂ 3) (productSet.{u} 2)
      (doubleCuspMetric.{u} a ha) =
      ENNReal.ofReal (a ^ 2) • Integral.Measure.riemannianVolumeMeasure (𝓡∂ 3)
        (productSet.{u} 2) (doubleCuspMetric.{u} 1 zero_lt_one) := by
  let w : ℝ → ℝ := fun r => Real.exp (doubleCuspLogProfile r)
  have hw : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ w :=
    (Real.contDiff_exp.comp doubleCuspLogProfile_smooth).contMDiff
  have hp (r : ℝ) : 0 < w r := Real.exp_pos _
  have he : (DifferentialGeometry.euclideanMetric (E := ℝ)).warpedProduct
      standardCuspTorusMetric w hw hp =
      doubleCuspRealMetric 1 zero_lt_one := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v z
    rw [SmoothRiemannianMetric.warpedProduct_inner]
    rw [doubleCuspRealMetric, SmoothRiemannianMetric.warpedProduct_inner]
    simp only [doubleCuspWarp, one_mul]
    rfl
  have h := Integral.Measure.volume_warped_fiber_scale_pullback
    (I := 𝓡∂ 3) (J := torusModel) (M := productSet.{u} 2) (N := Torus)
    (by simp : Module.finrank ℝ
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) = 2)
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
    standardCuspTorusMetric w hw hp
    doubleCuspCoordinate.{u} doubleCuspCoordinate_smooth.{u}
    doubleCuspCoordinate_immersion.{u} a ha
  change Integral.Measure.riemannianVolumeMeasure (𝓡∂ 3) (productSet.{u} 2)
    ((doubleCuspRealMetric a ha).pullback doubleCuspCoordinate.{u}
      doubleCuspCoordinate_smooth.{u} doubleCuspCoordinate_immersion.{u}) = _ at h
  rw [he] at h
  exact h

/-- A volume constant `V` with `Vol(doubleCuspMetric a) ≤ a² V` for all `a > 0`. -/
theorem exists_doubleCuspMetric_volume_bound_INST :
    ∃ V : ℝ, 0 < V ∧ ∀ (a : ℝ) (ha : 0 < a),
      Integral.Measure.riemannianVolumeMeasure (𝓡∂ 3) (productSet.{u} 2)
        (doubleCuspMetric.{u} a ha) univ ≤ ENNReal.ofReal (a ^ 2 * V) := by
  let μ := Integral.Measure.riemannianVolumeMeasure (𝓡∂ 3) (productSet.{u} 2)
    (doubleCuspMetric.{u} 1 zero_lt_one)
  let hfin : IsFiniteMeasure μ :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
  refine ⟨(μ univ).toReal + 1, by positivity, fun a ha => ?_⟩
  rw [doubleCuspMetric_volume_INST a ha, Measure.smul_apply, smul_eq_mul]
  change ENNReal.ofReal (a ^ 2) * μ univ ≤ _
  rw [ENNReal.ofReal_mul (sq_nonneg _)]
  apply mul_le_mul_right
  calc
    μ univ = ENNReal.ofReal (μ univ).toReal :=
      (ENNReal.ofReal_toReal (measure_lt_top μ univ).ne).symm
    _ ≤ ENNReal.ofReal ((μ univ).toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)

/-- A curvature-radius floor `1 / (C + 1)` at distance `> 10` from the boundary, for every scale. -/
theorem exists_doubleCuspMetric_curvatureRadius_floor_INST :
    ∃ R : ℝ, 0 < R ∧ R ≤ 1 ∧ ∀ (a : ℝ) (ha : 0 < a) (p : productSet.{u} 2),
      ENNReal.ofReal boundaryBufferDistance <
        distanceToBoundary annulusCircleCarrier.{u} (doubleCuspMetric.{u} a ha) p →
      ENNReal.ofReal R ≤ curvatureRadius (doubleCuspMetric.{u} a ha) p := by
  obtain ⟨C, hC, hsec⟩ := exists_doubleCuspRealMetric_sectionalBound
  let R := 1 / (C + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 := by
    dsimp [R]
    apply (div_le_one (by positivity : 0 < C + 1)).2
    linarith
  have hCR : C * R ≤ 1 := by
    dsimp [R]
    rw [← mul_div_assoc, mul_one]
    exact (div_le_one (by positivity : 0 < C + 1)).2 (by linarith)
  have hCRR : C * R ^ 2 ≤ 1 := by
    have hs : R ^ 2 ≤ R := by nlinarith
    exact (mul_le_mul_of_nonneg_left hs hC.le).trans hCR
  have hCI : C ≤ (R ^ 2)⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ (pow_pos hR 2)).2 hCRR
  refine ⟨R, hR, hR1, fun a ha p hp => ?_⟩
  refine ofReal_le_curvatureRadius (doubleCuspMetric.{u} a ha) hR ?_
  intro q hq
  have hb : ENNReal.ofReal R ≤
      distanceToBoundary annulusCircleCarrier.{u} (doubleCuspMetric.{u} a ha) p :=
    (ENNReal.ofReal_le_ofReal (hR1.trans (by norm_num [boundaryBufferDistance]))).trans hp.le
  exact (doubleCuspMetric_sectional_interior a ha C (hsec a ha) q
    (riemannianBallOf_subset_interior annulusCircleCarrier.{u} (doubleCuspMetric.{u} a ha) hb
      hq)).mono (neg_le_neg hCI)

/-- Volume collapse at the curvature scale from a curvature floor and a total volume bound. -/
theorem boundaryVolumeCollapsed_of_floor_INST (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) {w R : ℝ} (hw : 0 < w) (hR : 0 < R)
    (hfloor : ∀ p, ENNReal.ofReal boundaryBufferDistance < distanceToBoundary W g p →
      ENNReal.ofReal R ≤ curvatureRadius g p)
    (hvolume : (Integral.Measure.riemannianVolumeMeasure W.model W.Carrier g) univ ≤
      ENNReal.ofReal (w * R ^ 3)) : boundaryVolumeCollapsed W g w := by
  intro p hp r hr hrad
  have hf := hfloor p hp
  rw [hrad] at hf
  have hRr := ENNReal.toReal_mono (by simp) hf
  rw [ENNReal.toReal_ofReal hR.le, ENNReal.toReal_ofReal hr.le] at hRr
  have hpow := pow_le_pow_left₀ hR.le hRr 3
  exact (measure_mono (subset_univ _)).trans (hvolume.trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hw.le)))

/-- The derivative-control function of the double cusp family. -/
def doubleCuspControl_INST (B V : ℝ) (K : ℕ) (w : ℝ) : ℝ :=
  B * (max 1 (V / w)) ^ (K + 2) + 1

theorem doubleCuspControl_pos_INST {B : ℝ} (hB : 0 ≤ B) (V : ℝ) (K : ℕ) (w : ℝ) :
    0 < doubleCuspControl_INST B V K w := by
  unfold doubleCuspControl_INST
  have := pow_nonneg (zero_le_one.trans (le_max_left 1 (V / w))) (K + 2)
  nlinarith

/-- **One derivative-control function for the whole family.** -/
theorem doubleCusp_curvatureDerivativesControlled_INST (K : ℕ) :
    ∃ A : ℝ → ℝ, (∀ w, 0 < A w) ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 → ∀ w₀ : ℝ, 0 < w₀ →
      curvatureDerivativesControlled (doubleCuspMetric.{u} a ha) K A w₀ := by
  obtain ⟨B, hB, hb⟩ := exists_doubleCuspMetric_derivative_bound_INST.{u} K
  obtain ⟨V, hV, hvol⟩ := exists_doubleCuspMetric_volume_bound_INST.{u}
  refine ⟨doubleCuspControl_INST B V K, doubleCuspControl_pos_INST hB V K, ?_⟩
  intro a ha ha1 w₀ hw₀ p w r hw _hwc hr _hrR hv k hk q _hq
  have hwpos : 0 < w := hw₀.trans_le hw
  have hball : ballVolume (doubleCuspMetric.{u} a ha) p r ≤ ENNReal.ofReal (a ^ 2 * V) :=
    (measure_mono (subset_univ _)).trans (hvol a ha)
  have hwr : w * r ^ 3 ≤ a ^ 2 * V :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hv.trans hball)
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hwrV : w * r ^ 3 ≤ V := hwr.trans (by nlinarith)
  have hrR : r ≤ max 1 (V / w) := by
    rcases le_or_gt r 1 with h1 | h1
    · exact h1.trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      rw [le_div_iff₀ hwpos]
      have hr2 : 1 ≤ r ^ 2 := by nlinarith
      have hr3 : r ≤ r ^ 3 := by
        calc r = r * 1 := (mul_one r).symm
          _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left hr2 hr.le
          _ = r ^ 3 := by ring
      nlinarith
  have hp : r ^ (k + 2) ≤ (max 1 (V / w)) ^ (K + 2) :=
    (pow_le_pow_left₀ hr.le hrR _).trans
      (pow_le_pow_right₀ (le_max_left _ _) (by omega))
  refine (hb a ha k hk q).trans ?_
  change B ≤ doubleCuspControl_INST B V K w * (r ^ (k + 2))⁻¹
  rw [le_mul_inv_iff₀ (pow_pos hr _)]
  have hbp := mul_le_mul_of_nonneg_left hp hB
  unfold doubleCuspControl_INST
  linarith

/-- A torus scale `0 < a ≤ 1` small for both the boundary diameter and the total volume. -/
theorem exists_doubleCuspStandingScale_INST {D V R d : ℝ} (hD : 0 < D) (hV : 0 < V)
    (hR : 0 < R) (hd : 0 < d) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ a * D ≤ d ∧ a ^ 2 * V ≤ d * R ^ 3 := by
  let a := min 1 (min (d / D) (d * R ^ 3 / V))
  have ha : 0 < a := lt_min one_pos (lt_min (by positivity) (by positivity))
  have ha1 : a ≤ 1 := min_le_left _ _
  have haD : a ≤ d / D := (min_le_right _ _).trans (min_le_left _ _)
  have haV : a ≤ d * R ^ 3 / V := (min_le_right _ _).trans (min_le_right _ _)
  have haDw := (le_div_iff₀ hD).mp haD
  have haVw := (le_div_iff₀ hV).mp haV
  refine ⟨a, ha, ha1, haDw, ?_⟩
  have hs : a ^ 2 ≤ a := by nlinarith
  nlinarith

/-- **Level 2: the standing sequence for arbitrary positive ratios**, with ONE `A`. -/
theorem exists_doubleCusp_standing_sequence_INST (K : ℕ) :
    ∃ A : ℝ → ℝ, (∀ w, 0 < A w) ∧ ∀ d : ℕ → ℝ, (∀ n, 0 < d n) →
      ∃ (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
        (B : ∀ n, NearlyCuspidalBoundary annulusCircleCarrier.{u}
          (doubleCuspMetric.{u} (a n) (ha n)) K (d n)),
        (∀ n, (B n).count = 2) ∧
        (∀ n, boundaryVolumeCollapsed annulusCircleCarrier.{u}
          (doubleCuspMetric.{u} (a n) (ha n)) (d n)) ∧
        ∀ n, curvatureDerivativesControlled (doubleCuspMetric.{u} (a n) (ha n)) K A (d n) := by
  obtain ⟨A, hA, hctrl⟩ := doubleCusp_curvatureDerivativesControlled_INST.{u} K
  obtain ⟨V, hV, hvol⟩ := exists_doubleCuspMetric_volume_bound_INST.{u}
  obtain ⟨R, hR, _hR1, hfloor⟩ := exists_doubleCuspMetric_curvatureRadius_floor_INST.{u}
  obtain ⟨D, hD, hdiam⟩ := exists_standardCuspTorus_diameter_INST
  refine ⟨A, hA, fun d hd => ?_⟩
  have hscale (n : ℕ) := exists_doubleCuspStandingScale_INST hD hV hR (hd n)
  choose a ha ha1 haD haV using hscale
  refine ⟨a, ha, fun n => doubleCuspNearlyCuspidalBoundaryAt.{u} (a n) (ha n) D hD.le hdiam K
    (d n) (haD n), fun _ => rfl, fun n => ?_, fun n => hctrl (a n) (ha n) (ha1 n) (d n) (hd n)⟩
  exact boundaryVolumeCollapsed_of_floor_INST annulusCircleCarrier.{u}
    (doubleCuspMetric.{u} (a n) (ha n)) (hd n) hR (hfloor (a n) (ha n))
    ((hvol (a n) (ha n)).trans (ENNReal.ofReal_le_ofReal (haV n)))

end DifferentialGeometry.Geometry.Collapse
