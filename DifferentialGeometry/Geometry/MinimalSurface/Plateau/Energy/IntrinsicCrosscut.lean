import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.IntrinsicPolar
import DifferentialGeometry.Analysis.Integration.PolarAnnulus.Centered
import DifferentialGeometry.Analysis.Integration.Integral.LogRadiusSelection
import DifferentialGeometry.Analysis.Complex.CircleArc
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Lipschitz
import DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacherSource
import DifferentialGeometry.Analysis.Integration.Measure.Polar.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

section

noncomputable section

open Set Filter MeasureTheory Manifold Metric
open DifferentialGeometry.Analysis
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

private def maskedCircleDirectionalEnergy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : ℂ → M) (Ω : Set ℂ) (c : ℂ)
    (ρ : ℝ) : ℝ :=
  ∫ θ in Icc (-Real.pi) Real.pi, ρ⁻¹ *
    Ω.indicator (diskMapDirectionalEnergyDensity g u (fun z => (z - c) * Complex.I))
      (circleMap c ρ θ)

private theorem integrableOn_maskedCircleDirectionalEnergy_and_integral_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {K : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (K : ℝ≥0∞) * edist z w)
    {Ω : Set ℂ} (hΩ : MeasurableSet Ω) (c : ℂ)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    IntegrableOn (maskedCircleDirectionalEnergy g u Ω c) (Icc r R) ∧
      (∫ ρ in Icc r R, maskedCircleDirectionalEnergy g u Ω c ρ) ≤
        2 * ∫ z in {z : ℂ | dist z c ∈ Icc r R} ∩ Ω, diskMapEnergyDensity g u z := by
  classical
  let Q := Ω.indicator
    (diskMapDirectionalEnergyDensity g u (fun z => (z - c) * Complex.I))
  let H := Ω.indicator (diskMapEnergyDensity g u)
  let A : ℝ × ℝ → ℝ := fun p => p.1⁻¹ * Q (circleMap c p.1 p.2)
  let D : ℝ × ℝ → ℝ := fun p => 2 * p.1 * H (circleMap c p.1 p.2)
  have huc := continuous_of_riemannian_lipschitz g hu
  have hQm : Measurable Q :=
    (measurable_diskMapDirectionalEnergyDensity g huc (by fun_prop)).indicator hΩ
  have hHm : Measurable H := (measurable_diskMapEnergyDensity g huc).indicator hΩ
  have hcm : Measurable (fun p : ℝ × ℝ => circleMap c p.1 p.2) := by
    unfold circleMap
    fun_prop
  have hAm : Measurable A := measurable_fst.inv.mul (hQm.comp hcm)
  have hDm : Measurable D := (measurable_const.mul measurable_fst).mul (hHm.comp hcm)
  have hHnonneg (z : ℂ) : 0 ≤ H z := by
    by_cases hz : z ∈ Ω
    · simp only [H, indicator_of_mem hz, diskMapEnergyDensity]
      exact div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
        (metric_inner_self_nonneg g _ _)) (by norm_num)
    · simp only [H, indicator_of_notMem hz, le_refl]
  have hQnonneg (z : ℂ) : 0 ≤ Q z := by
    by_cases hz : z ∈ Ω
    · simpa only [Q, indicator_of_mem hz] using
        diskMapDirectionalEnergyDensity_nonneg g u (fun z => (z - c) * Complex.I) z
    · simp only [Q, indicator_of_notMem hz, le_refl]
  have hHbound (z : ℂ) : H z ≤ (K : ℝ) ^ 2 := by
    by_cases hz : z ∈ Ω
    · simpa only [H, indicator_of_mem hz] using diskMapEnergyDensity_le_of_lipschitz g hu z
    · simpa only [H, indicator_of_notMem hz] using sq_nonneg (K : ℝ)
  have hAD (p : ℝ × ℝ) (hp : 0 < p.1) : A p ≤ D p := by
    by_cases hz : circleMap c p.1 p.2 ∈ Ω
    · have hq := diskMapPartial_inner_self_le g u (circleMap c p.1 p.2)
        ((circleMap c p.1 p.2 - c) * Complex.I)
      have hvnorm : ‖(circleMap c p.1 p.2 - c) * Complex.I‖ ^ 2 = p.1 ^ 2 := by
        simp [circleMap, abs_of_pos hp]
      rw [hvnorm] at hq
      change diskMapDirectionalEnergyDensity g u (fun z => (z - c) * Complex.I)
        (circleMap c p.1 p.2) ≤ _ at hq
      dsimp only [A, D, Q, H]
      rw [indicator_of_mem hz, indicator_of_mem hz]
      apply (mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr hp.le)).trans_eq
      field_simp
    · simp only [A, D, Q, H, indicator_of_notMem hz, mul_zero, le_refl]
  have hDi : IntegrableOn D (Icc (r, -Real.pi) (R, Real.pi)) := by
    apply (integrableOn_const (C := 2 * R * (K : ℝ) ^ 2)
      isCompact_Icc.measure_ne_top).mono' hDm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with p hp
    have hp0 : 0 ≤ p.1 := (hr.trans_le hp.1.1).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hHnonneg _))]
    exact mul_le_mul (by nlinarith [hp.2.1]) (hHbound _)
      (hHnonneg _) (by nlinarith [hr.trans_le hrR])
  have hAi : IntegrableOn A (Icc (r, -Real.pi) (R, Real.pi)) := by
    apply hDi.mono' hAm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with p hp
    have hp0 := hr.trans_le hp.1.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hp0.le) (hQnonneg _))]
    exact hAD p hp0
  have hAprod : Integrable A
      ((volume.restrict (Icc r R)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod, Icc_prod_Icc]
    exact hAi
  refine ⟨hAprod.integral_prod_left, ?_⟩
  change (∫ ρ in Icc r R, ∫ θ in Icc (-Real.pi) Real.pi, A (ρ, θ)) ≤ _
  have hleft : (∫ p in Icc (r, -Real.pi) (R, Real.pi), A p) =
      ∫ ρ in Icc r R, ∫ θ in Icc (-Real.pi) Real.pi, A (ρ, θ) := by
    rw [← Icc_prod_Icc, Measure.volume_eq_prod]
    exact setIntegral_prod A (by rwa [← Measure.volume_eq_prod, Icc_prod_Icc])
  rw [← hleft]
  have hright : (∫ p in Icc (r, -Real.pi) (R, Real.pi), D p) =
      2 * ∫ z in {z : ℂ | dist z c ∈ Icc r R} ∩ Ω, diskMapEnergyDensity g u z := by
    simp only [D, mul_assoc, integral_const_mul]
    have hp := integral_annulus_eq_circleMap H c (R := R) hr
    simp only [smul_eq_mul] at hp
    rw [← hp, setIntegral_indicator hΩ]
  rw [← hright]
  apply integral_mono_ae hAi hDi
  filter_upwards [ae_restrict_mem measurableSet_Icc] with p hp
  exact hAD p (hr.trans_le hp.1.1)

private theorem integral_affine_parameter_sq (q : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Icc (0 : ℝ) 1, (b - a) ^ 2 * q (a + (b - a) * t)) =
      (b - a) * ∫ θ in Icc a b, q θ := by
  rw [integral_const_mul]
  have h := intervalIntegral.smul_integral_comp_add_mul
    (a := (0 : ℝ)) (b := 1) q (b - a) a
  have hb : a + (b - a) * 1 = b := by ring
  simp only [mul_zero, add_zero, hb, smul_eq_mul] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc] at h
  calc
    _ = (b - a) * ((b - a) * ∫ t in Icc (0 : ℝ) 1, q (a + (b - a) * t)) := by ring
    _ = _ := by rw [h]

private theorem integral_normalized_arc_speed_sq_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {K : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (K : ℝ≥0∞) * edist z w)
    {Ω : Set ℂ} (hΩ : MeasurableSet Ω) (c : ℂ) {ρ a b : ℝ} (hρ : 0 < ρ)
    (ha : a ∈ Icc (-Real.pi) Real.pi) (hb : b ∈ Icc (-Real.pi) Real.pi) (hab : a < b)
    (harc : MapsTo (circleMap c ρ) (Icc a b) Ω)
    (hdiff : ∀ᵐ θ ∂volume.restrict (Icc (-Real.pi) Real.pi),
      MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u (circleMap c ρ θ)) :
    IntegrableOn (fun t => (riemannianCurveSpeed g
      (fun s => u (circleMap c ρ (a + (b - a) * s))) t) ^ 2) (Icc (0 : ℝ) 1) ∧
      (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g
        (fun s => u (circleMap c ρ (a + (b - a) * s))) t) ^ 2) ≤
        (b - a) * ρ * maskedCircleDirectionalEnergy g u Ω c ρ := by
  classical
  let Q := Ω.indicator
    (diskMapDirectionalEnergyDensity g u (fun z => (z - c) * Complex.I))
  let q : ℝ → ℝ := fun θ => Q (circleMap c ρ θ)
  have hqm : Measurable q :=
    ((measurable_diskMapDirectionalEnergyDensity g (continuous_of_riemannian_lipschitz g hu)
      (by fun_prop)).indicator hΩ).comp (continuous_circleMap c ρ).measurable
  have hq0 (θ : ℝ) : 0 ≤ q θ := by
    by_cases hz : circleMap c ρ θ ∈ Ω
    · simpa only [q, Q, indicator_of_mem hz] using
        diskMapDirectionalEnergyDensity_nonneg g u (fun z => (z - c) * Complex.I) _
    · simp only [q, Q, indicator_of_notMem hz, le_refl]
  have hqbound (θ : ℝ) : q θ ≤ ((K : ℝ) * ρ) ^ 2 := by
    by_cases hz : circleMap c ρ θ ∈ Ω
    · have h := diskMapDirectionalEnergyDensity_le_of_lipschitz g hu
        (fun z => (z - c) * Complex.I) (circleMap c ρ θ)
      simpa only [q, Q, indicator_of_mem hz] using (show
        diskMapDirectionalEnergyDensity g u (fun z => (z - c) * Complex.I)
          (circleMap c ρ θ) ≤ ((K : ℝ) * ρ) ^ 2 by
        simpa [circleMap, norm_mul, abs_of_pos hρ] using h)
    · simpa only [q, Q, indicator_of_notMem hz] using sq_nonneg ((K : ℝ) * ρ)
  have hqi : IntegrableOn q (Icc (-Real.pi) Real.pi) := by
    apply (integrableOn_const (C := ((K : ℝ) * ρ) ^ 2)
      isCompact_Icc.measure_ne_top).mono' hqm.aestronglyMeasurable
    exact Eventually.of_forall fun θ => by
      rw [Real.norm_of_nonneg (hq0 θ)]
      exact hqbound θ
  let k := b - a
  have hk : 0 < k := sub_pos.mpr hab
  let l : ℝ → ℝ := fun t => a + k * t
  have hlmap : MapsTo l (Icc (0 : ℝ) 1) (Icc a b) := by
    intro t ht
    dsimp only [l, k]
    constructor <;> nlinarith [ht.1, ht.2]
  have hql : Measure.QuasiMeasurePreserving l volume volume := by
    simpa only [l, smul_eq_mul, Function.comp_def] using
      ((measurePreserving_add_left (volume : Measure ℝ) a).quasiMeasurePreserving.comp
        (Measure.quasiMeasurePreserving_smul volume hk.ne'))
  have hd : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u (circleMap c ρ (l t)) :=
    (hql.restrict (s := Icc (0 : ℝ) 1) (t := Icc (-Real.pi) Real.pi)
      (hlmap.mono_right (Icc_subset_Icc ha.1 hb.2))).ae hdiff
  have hspeed : (fun t => (riemannianCurveSpeed g
      (fun s => u (circleMap c ρ (a + (b - a) * s))) t) ^ 2) =ᵐ[
        volume.restrict (Icc (0 : ℝ) 1)] (fun t => k ^ 2 * q (l t)) := by
    filter_upwards [hd, ae_restrict_mem measurableSet_Icc] with t ht htI
    have hder : HasDerivAt (fun s => circleMap c ρ (l s))
        (k • (circleMap 0 ρ (l t) * Complex.I)) t := by
      simpa only [l, Function.comp_def, mul_one] using
        (hasDerivAt_circleMap c ρ (l t)).scomp t
          ((hasDerivAt_id t).const_mul k |>.const_add a)
    have hsp := riemannianCurveSpeed_comp g
      (r := u) (v := fun s => circleMap c ρ (l s)) (t := t) ht hder.differentiableAt
    have hvel : (circleMap c ρ (l t) - c) * Complex.I =
        circleMap 0 ρ (l t) * Complex.I := by simp [circleMap]
    erw [hder.deriv] at hsp
    change (riemannianCurveSpeed g (u ∘ fun s => circleMap c ρ (l s)) t) ^ 2 = _
    rw [hsp, Real.sq_sqrt (metric_inner_self_nonneg g _ _)]
    simp only [q, Q, indicator_of_mem (harc (hlmap htI)),
      diskMapDirectionalEnergyDensity, hvel]
    let L : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u (circleMap c ρ (l t))
    let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (u (circleMap c ρ (l t)))
    let v : ℂ := circleMap 0 ρ (l t) * Complex.I
    change B (L (k • v)) (L (k • v)) = k ^ 2 * B (L v) (L v)
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have htargeti : IntegrableOn (fun t => k ^ 2 * q (l t)) (Icc (0 : ℝ) 1) := by
    apply (integrableOn_const (C := k ^ 2 * ((K : ℝ) * ρ) ^ 2)
      isCompact_Icc.measure_ne_top).mono'
      ((measurable_const.mul (hqm.comp (by dsimp only [l]; fun_prop))).aestronglyMeasurable)
    exact Eventually.of_forall fun t => by
      change ‖k ^ 2 * q (l t)‖ ≤ k ^ 2 * ((K : ℝ) * ρ) ^ 2
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg k) (hq0 _))]
      exact mul_le_mul_of_nonneg_left (hqbound _) (sq_nonneg k)
  refine ⟨htargeti.congr hspeed.symm, ?_⟩
  rw [integral_congr_ae hspeed]
  change (∫ t in Icc (0 : ℝ) 1, (b - a) ^ 2 * q (a + (b - a) * t)) ≤ _
  rw [integral_affine_parameter_sq q hab.le]
  have hmono := setIntegral_mono_set hqi (Eventually.of_forall hq0)
    (Eventually.of_forall (Icc_subset_Icc ha.1 hb.2))
  have hmask : ρ * maskedCircleDirectionalEnergy g u Ω c ρ =
      ∫ θ in Icc (-Real.pi) Real.pi, q θ := by
    unfold maskedCircleDirectionalEnergy
    rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]
  rw [mul_assoc, hmask]
  exact mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hab.le)

theorem exists_radius_normalized_crosscut_riemannian_energy_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {K : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (K : ℝ≥0∞) * edist z w)
    {r R B : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < 2)
    (henergy : (∫ z in {z : ℂ | dist z (-1) ∈ Icc r R} ∩
      closedBall (0 : ℂ) 1, diskMapEnergyDensity g u z) ≤ B) :
    ∃ ρ ∈ Ioo r R,
      let a := Real.arccos (ρ / 2)
      IntegrableOn (fun t => (riemannianCurveSpeed g
        (fun s => u (circleMap (-1) ρ (-a + (2 * a) * s))) t) ^ 2) (Icc (0 : ℝ) 1) ∧
      (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g
        (fun s => u (circleMap (-1) ρ (-a + (2 * a) * s))) t) ^ 2) ≤
          2 * Real.pi * B / Real.log (R / r) := by
  have htrans := (measurePreserving_add_left (volume : Measure ℂ) (-1)).quasiMeasurePreserving
  have hshift : ∀ᵐ z : ℂ, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u ((-1 : ℂ) + z) :=
    htrans.tendsto_ae.eventually
      (ae_mdifferentiableAt_of_metric_lipschitz g hu)
  have hdiff : ∀ᵐ ρ ∂volume.restrict (Ioo r R),
      ∀ᵐ θ ∂volume.restrict (Icc (-Real.pi) Real.pi),
        MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u (circleMap (-1) ρ θ) := by
    have h := ae_restrict_of_ae_restrict_of_subset
      (show Ioo r R ⊆ Ioi (0 : ℝ) from fun x hx => hr.trans hx.1)
      (ae_ae_comp_circleMap hshift)
    simpa only [circleMap, zero_add] using h
  let N := {ρ : ℝ | ¬ ∀ᵐ θ ∂volume.restrict (Icc (-Real.pi) Real.pi),
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u (circleMap (-1) ρ θ)}
  have hN : (volume.restrict (Ioo r R)) N = 0 := ae_iff.mp hdiff
  obtain ⟨hi, hbound⟩ := integrableOn_maskedCircleDirectionalEnergy_and_integral_le
    g hu measurableSet_closedBall (-1) hr hrR.le
  obtain ⟨ρ, hρ, hρN, hρenergy⟩ := exists_mul_le_div_log_notMem_null hr hrR hi hN
    (hbound.trans (mul_le_mul_of_nonneg_left henergy (by norm_num : (0 : ℝ) ≤ 2)))
  have hρdiff : ∀ᵐ θ ∂volume.restrict (Icc (-Real.pi) Real.pi),
      MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u (circleMap (-1) ρ θ) := by
    simpa only [N, mem_ofPred_eq, not_not] using hρN
  let a := Real.arccos (ρ / 2)
  have hρ0 : 0 < ρ := hr.trans hρ.1
  have hρ2 : ρ < 2 := hρ.2.trans hR
  have ha0 : 0 < a := Real.arccos_pos.mpr (by linarith)
  have haπ : a ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr (by positivity)
  have hma : -a ∈ Icc (-Real.pi) Real.pi := by constructor <;> nlinarith [Real.pi_pos]
  have hpa : a ∈ Icc (-Real.pi) Real.pi := by constructor <;> nlinarith [Real.pi_pos]
  obtain ⟨hinti, hle⟩ := integral_normalized_arc_speed_sq_le g hu measurableSet_closedBall (-1)
    hρ0 hma hpa (by linarith : -a < a)
    (fun θ hθ => Complex.circleMap_neg_one_mem_closedBall ρ hρ0.le hρ2.le hθ) hρdiff
  have hid : a - -a = 2 * a := by ring
  simp only [hid] at hinti hle
  refine ⟨ρ, hρ, hinti, ?_⟩
  have hm0 : 0 ≤ maskedCircleDirectionalEnergy g u (closedBall (0 : ℂ) 1) (-1) ρ := by
    unfold maskedCircleDirectionalEnergy
    apply integral_nonneg
    intro θ
    apply mul_nonneg (inv_nonneg.mpr hρ0.le)
    apply indicator_nonneg
    intro z hz
    exact diskMapDirectionalEnergyDensity_nonneg g u _ z
  calc
    _ ≤ (2 * a) * ρ * maskedCircleDirectionalEnergy g u (closedBall (0 : ℂ) 1) (-1) ρ := hle
    _ ≤ Real.pi * (ρ * maskedCircleDirectionalEnergy g u (closedBall (0 : ℂ) 1) (-1) ρ) := by
      have h := mul_le_mul_of_nonneg_right
        (show 2 * a ≤ Real.pi by linarith) (mul_nonneg hρ0.le hm0)
      simpa only [mul_assoc] using h
    _ ≤ Real.pi * ((2 * B) / Real.log (R / r)) :=
      mul_le_mul_of_nonneg_left hρenergy Real.pi_pos.le
    _ = _ := by ring

end DifferentialGeometry.Geometry

end

end
