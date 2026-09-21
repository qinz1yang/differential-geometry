import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus
import Mathlib.MeasureTheory.Integral.CircleIntegral
import DifferentialGeometry.Geometry.Measure.Area.DirectionalEnergy
import DifferentialGeometry.Analysis.Integration.Measure.Polar.Complex
import DifferentialGeometry.Analysis.Integration.PolarAnnulus
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Lipschitz
import DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacherSource
import Mathlib.MeasureTheory.Integral.Average
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Affine

section

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem diskMapPartial_inner_self_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (z v : ℂ) :
    g.inner (U z) (diskMapPartial U z v) (diskMapPartial U z v) ≤
      2 * ‖v‖ ^ 2 * diskMapEnergyDensity g U z := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have hpartial : diskMapPartial (E := E) U z v =
      v.re • diskMapPartial U z 1 + v.im • diskMapPartial U z Complex.I := by
    unfold diskMapPartial
    erw [← map_smul, ← map_smul, ← map_add]
    exact congrArg (fun q : ℂ => (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z q : E)) hv
  let w : TangentSpace 𝓘(ℝ, E) (U z) :=
    v.im • diskMapPartial U z 1 - v.re • diskMapPartial U z Complex.I
  have hsum :
      g.inner (U z) (diskMapPartial U z v) (diskMapPartial U z v) +
        g.inner (U z) w w = 2 * ‖v‖ ^ 2 * diskMapEnergyDensity g U z := by
    rw [hpartial]
    simp only [w, diskMapEnergyDensity, map_add, map_sub, map_smul,
      add_apply, sub_apply, smul_apply, smul_eq_mul]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  exact (le_add_of_nonneg_right (metric_inner_self_nonneg g (U z) w)).trans_eq hsum

theorem riemannianCurveSpeed_sq_comp_le_diskMapEnergyDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {c : ℝ → ℂ} {t : ℝ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (c t))
    (hc : DifferentiableAt ℝ c t) :
    (riemannianCurveSpeed g (U ∘ c) t) ^ 2 ≤
      2 * ‖deriv c t‖ ^ 2 * diskMapEnergyDensity g U (c t) := by
  rw [riemannianCurveSpeed_comp g hU hc,
    Real.sq_sqrt (metric_inner_self_nonneg g _ _)]
  exact diskMapPartial_inner_self_le g U (c t) (deriv c t)

theorem riemannianCurveSpeed_sq_comp_circleMap_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} (b : ℂ) (ρ t : ℝ)
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U
      (circleMap b ρ (2 * Real.pi * t - Real.pi))) :
    (riemannianCurveSpeed g
      (fun s => U (circleMap b ρ (2 * Real.pi * s - Real.pi))) t) ^ 2 ≤
      2 * (2 * Real.pi * ρ) ^ 2 *
        diskMapEnergyDensity g U (circleMap b ρ (2 * Real.pi * t - Real.pi)) := by
  have hθ : HasDerivAt (fun s : ℝ => 2 * Real.pi * s - Real.pi) (2 * Real.pi) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * Real.pi)).sub_const Real.pi
  have hc : HasDerivAt (fun s => circleMap b ρ (2 * Real.pi * s - Real.pi))
      ((2 * Real.pi) • (circleMap 0 ρ (2 * Real.pi * t - Real.pi) * Complex.I)) t := by
    simpa only [Function.comp_def] using
      (hasDerivAt_circleMap b ρ (2 * Real.pi * t - Real.pi)).scomp t hθ
  have hnorm : ‖deriv (fun s => circleMap b ρ (2 * Real.pi * s - Real.pi)) t‖ ^ 2 =
      (2 * Real.pi * ρ) ^ 2 := by
    rw [hc.deriv]
    simp only [norm_smul, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero,
      Real.norm_eq_abs, mul_pow, sq_abs]
  have h := riemannianCurveSpeed_sq_comp_le_diskMapEnergyDensity g
    (c := fun s => circleMap b ρ (2 * Real.pi * s - Real.pi)) (t := t) hU hc.differentiableAt
  rw [hnorm] at h
  exact h

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

set_option backward.isDefEq.respectTransparency false in
theorem integrableOn_and_integral_circle_speed_sq_le_disk_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {K : ℝ≥0}
    (hu : ∀ z z', riemannianEDistOf g (u z) (u z') ≤ (K : ℝ≥0∞) * edist z z')
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    (∀ᵐ ρ ∂volume.restrict (Icc r R), IntegrableOn (fun t =>
      (riemannianCurveSpeed g (fun s => u (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t) ^ 2)
        (Icc (0 : ℝ) 1)) ∧
      IntegrableOn (fun ρ => ∫ t in Icc (0 : ℝ) 1,
        (riemannianCurveSpeed g (fun s => u (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t) ^ 2)
        (Icc r R) ∧
      (∫ ρ in Icc r R, ∫ t in Icc (0 : ℝ) 1,
        (riemannianCurveSpeed g (fun s => u (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t) ^ 2) ≤
          (4 * Real.pi * R) * ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, diskMapEnergyDensity g u z := by
  let μ := volume.restrict (Icc r R)
  let ν := volume.restrict (Icc (0 : ℝ) 1)
  let c : ℝ × ℝ → ℂ := fun p => circleMap 0 p.1 (2 * Real.pi * p.2 - Real.pi)
  let v : ℝ × ℝ → ℂ := fun p => (2 * Real.pi) • (c p * Complex.I)
  let Q : ℝ × ℝ → ℝ := fun p => g.inner (u (c p))
    (diskMapPartial u (c p) (v p)) (diskMapPartial u (c p) (v p))
  let B : ℝ × ℝ → ℝ := fun p => (2 * Real.pi) * p.1 * diskMapEnergyDensity g u (c p)
  let q : ℝ → ℝ → ℝ := fun ρ t =>
    (riemannianCurveSpeed g (fun s => u (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t) ^ 2
  have hc : Continuous c := by unfold c circleMap; fun_prop
  have hv : Continuous v := by unfold v; fun_prop
  have humeas := measurable_diskMapEnergyDensity g (continuous_of_riemannian_lipschitz g hu)
  have hQmeas : Measurable Q :=
    (measurable_metric_mfderiv_apply g (continuous_of_riemannian_lipschitz g hu)).comp
      (hc.measurable.prodMk hv.measurable)
  have hBmeas : Measurable B :=
    (measurable_const.mul measurable_fst).mul (humeas.comp hc.measurable)
  have hEnonneg (z : ℂ) : 0 ≤ diskMapEnergyDensity g u z :=
    div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _) (metric_inner_self_nonneg g _ _))
      (by norm_num)
  have hQnonneg (p : ℝ × ℝ) : 0 ≤ Q p := metric_inner_self_nonneg g _ _
  have hvnorm (p : ℝ × ℝ) : ‖v p‖ ^ 2 = (2 * Real.pi * p.1) ^ 2 := by
    simp only [v, norm_smul, norm_mul, Complex.norm_I, mul_one, c, norm_circleMap_zero,
      Real.norm_eq_abs, mul_pow, sq_abs]
  have hrad : ∀ᵐ p ∂μ.prod ν, p.1 ∈ Icc r R :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have hR : 0 < R := hr.trans_le hrR
  have hQle (p : ℝ × ℝ) : Q p ≤ 2 * (2 * Real.pi * p.1) ^ 2 * diskMapEnergyDensity g u (c p) := by
    simpa only [Q, hvnorm] using diskMapPartial_inner_self_le g u (c p) (v p)
  have hQi : Integrable Q (μ.prod ν) := by
    apply Integrable.of_bound hQmeas.aestronglyMeasurable (2 * (2 * Real.pi * R) ^ 2 * (K : ℝ) ^ 2)
    filter_upwards [hrad] with p hp
    have hp0 : 0 ≤ p.1 := hr.le.trans hp.1
    rw [Real.norm_eq_abs, abs_of_nonneg (hQnonneg p)]
    apply (hQle p).trans
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [Real.pi_pos, hp.2]
    · exact diskMapEnergyDensity_le_of_lipschitz g hu (c p)
    · exact hEnonneg _
    · positivity
  have hBi : Integrable B (μ.prod ν) := by
    apply Integrable.of_bound hBmeas.aestronglyMeasurable ((2 * Real.pi) * R * (K : ℝ) ^ 2)
    filter_upwards [hrad] with p hp
    have hp0 : 0 ≤ p.1 := hr.le.trans hp.1
    dsimp only [B]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hEnonneg _))]
    exact mul_le_mul (by nlinarith [Real.pi_pos, hp.2])
      (diskMapEnergyDensity_le_of_lipschitz g hu _) (hEnonneg _) (by positivity)
  have hQB : ∀ᵐ p ∂μ.prod ν, Q p ≤ (4 * Real.pi * R) * B p := by
    filter_upwards [hrad] with p hp
    have hp0 : 0 ≤ p.1 := hr.le.trans hp.1
    have hρ : p.1 ^ 2 ≤ R * p.1 := by nlinarith [hp.2]
    apply (hQle p).trans
    have hfactor : 2 * (2 * Real.pi * p.1) ^ 2 ≤
        (4 * Real.pi * R) * ((2 * Real.pi) * p.1) := by
      nlinarith [mul_nonneg (sq_nonneg (2 * Real.pi)) (sub_nonneg.mpr hρ)]
    simpa only [B, mul_assoc] using mul_le_mul_of_nonneg_right hfactor (hEnonneg (c p))
  have hdiff := Analysis.ae_ae_comp_circleMap_normalized
    (ae_mdifferentiableAt_of_metric_lipschitz g hu) hr (R := R)
  have hqeq : ∀ᵐ ρ ∂μ, (q ρ) =ᵐ[ν] (fun t => Q (ρ, t)) := by
    filter_upwards [hdiff] with ρ hρ
    filter_upwards [hρ] with t ht
    have hθ : HasDerivAt (fun s : ℝ => 2 * Real.pi * s - Real.pi) (2 * Real.pi) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * Real.pi)).sub_const Real.pi
    have hcircle : HasDerivAt (fun s => circleMap 0 ρ (2 * Real.pi * s - Real.pi))
        ((2 * Real.pi) • (circleMap 0 ρ (2 * Real.pi * t - Real.pi) * Complex.I)) t := by
      simpa only [Function.comp_def] using
        (hasDerivAt_circleMap 0 ρ (2 * Real.pi * t - Real.pi)).scomp t hθ
    have hchain := riemannianCurveSpeed_comp g
      (v := fun s => circleMap 0 ρ (2 * Real.pi * s - Real.pi)) (t := t) ht hcircle.differentiableAt
    change q ρ t = Q (ρ, t)
    unfold q
    rw [show (fun s => u (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) =
      u ∘ (fun s => circleMap 0 ρ (2 * Real.pi * s - Real.pi)) from rfl, hchain, hcircle.deriv,
      Real.sq_sqrt (metric_inner_self_nonneg g _ _)]
    rfl
  have hqint : ∀ᵐ ρ ∂μ, Integrable (q ρ) ν := by
    filter_upwards [hQi.prod_right_ae, hqeq] with ρ hρ heq
    exact hρ.congr heq.symm
  have hqIeq : (fun ρ => ∫ t, q ρ t ∂ν) =ᵐ[μ] (fun ρ => ∫ t, Q (ρ, t) ∂ν) :=
    hqeq.mono fun ρ heq => integral_congr_ae heq
  have hqI : Integrable (fun ρ => ∫ t, q ρ t ∂ν) μ :=
    hQi.integral_prod_left.congr hqIeq.symm
  have hBint : (∫ ρ, ∫ t, B (ρ, t) ∂ν ∂μ) =
      ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, diskMapEnergyDensity g u z := by
    have hpolar := Analysis.integral_annulus_eq_integral_normalized_polar_of_bounded
      humeas hr (R := R) (B := (K : ℝ) ^ 2) (fun z _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hEnonneg z)]
        exact diskMapEnergyDensity_le_of_lipschitz g hu z)
    rw [← integral_prod _ hBi]
    change (∫ p, B p ∂μ.prod ν) = _
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    rw [hpolar, ← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro p
    have heq : Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi) = c p := by
      simp only [Complex.polarCoord_symm_apply, c, circleMap, zero_add,
        Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    change B p = (2 * Real.pi) * (p.1 * diskMapEnergyDensity g u
      (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)))
    rw [heq]
    dsimp only [B]
    ring
  refine ⟨hqint, hqI, ?_⟩
  change (∫ ρ, ∫ t, q ρ t ∂ν ∂μ) ≤ _
  rw [integral_congr_ae hqIeq, ← integral_prod _ hQi]
  have h := integral_mono_ae hQi (hBi.const_mul (4 * Real.pi * R)) hQB
  rw [integral_const_mul, integral_prod _ hBi, hBint] at h
  exact h

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Metric
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_radius_circle_energy_le_annular_disk_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {K : ℝ≥0}
    (hu : ∀ z z', riemannianEDistOf g (u z) (u z') ≤ (K : ℝ≥0∞) * edist z z')
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ ρ ∈ Icc r R,
      IntegrableOn (fun t => (riemannianCurveSpeed g
        (fun s => u (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t) ^ 2) (Icc (0 : ℝ) 1) ∧
      (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g
        (fun s => u (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t) ^ 2) ≤
        (4 * Real.pi * R / (R - r)) *
          ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, diskMapEnergyDensity g u z := by
  let μ := volume.restrict (Icc r R)
  let d : ℝ → ℝ := fun ρ => ∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g
    (fun s => u (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t) ^ 2
  obtain ⟨hint, hd, hbound⟩ :=
    integrableOn_and_integral_circle_speed_sq_le_disk_energy g hu hr hrR.le
  have hμreal : μ.real univ = R - r := by
    simp only [Measure.real, μ, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hrR.le)]
  have hμ : μ ≠ 0 := by
    intro hz
    have h := hμreal
    simp only [hz, Measure.real, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero] at h
    exact (sub_pos.mpr hrR).ne' h.symm
  let N : Set ℝ := {ρ | ¬ (ρ ∈ Icc r R ∧ IntegrableOn (fun t => (riemannianCurveSpeed g
    (fun s => u (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t) ^ 2) (Icc (0 : ℝ) 1))}
  have hN : μ N = 0 := by
    apply ae_iff.mp
    filter_upwards [ae_restrict_mem measurableSet_Icc, hint] with ρ hρ hi
    exact ⟨hρ, hi⟩
  obtain ⟨ρ, hρ, he⟩ := exists_notMem_null_le_average hμ hd hN
  have hP : ρ ∈ Icc r R ∧ IntegrableOn (fun t => (riemannianCurveSpeed g
      (fun s => u (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t) ^ 2) (Icc (0 : ℝ) 1) := by
    simpa only [N, mem_ofPred_eq, not_not] using hρ
  refine ⟨ρ, hP.1, hP.2, ?_⟩
  change d ρ ≤ _
  apply he.trans
  rw [average_eq, smul_eq_mul, hμreal]
  exact (mul_le_mul_of_nonneg_left hbound
    (inv_nonneg.mpr (sub_nonneg.mpr hrR.le))).trans_eq (by ring)

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Metric
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_radius_circle_energy_le_annular_disk_energy_at
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {K : ℝ≥0}
    (hu : ∀ z z', riemannianEDistOf g (u z) (u z') ≤ (K : ℝ≥0∞) * edist z z')
    (b : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ ρ ∈ Icc r R,
      IntegrableOn (fun t => (riemannianCurveSpeed g
        (fun s => u (b + ρ • circleMap 0 1 (2 * Real.pi * s - Real.pi))) t) ^ 2)
        (Icc (0 : ℝ) 1) ∧
      (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g
        (fun s => u (b + ρ • circleMap 0 1 (2 * Real.pi * s - Real.pi))) t) ^ 2) ≤
        (4 * Real.pi * R / (R - r)) *
          ∫ z in {z : ℂ | dist z b ∈ Icc r R}, diskMapEnergyDensity g u z := by
  let U : ℂ → M := fun z => u (b + z)
  have hU : ∀ z z', riemannianEDistOf g (U z) (U z') ≤ (K : ℝ≥0∞) * edist z z' := by
    intro z z'
    simpa only [edist_add_left] using hu (b + z) (b + z')
  have hd (z : ℂ) : diskMapEnergyDensity g U z = diskMapEnergyDensity g u (b + z) := by
    simpa only [U, one_smul, one_pow, one_mul] using
      diskMapEnergyDensity_comp_affine g u b z 1
  have hi : (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, diskMapEnergyDensity g U z) =
      ∫ z in {z : ℂ | dist z b ∈ Icc r R}, diskMapEnergyDensity g u z := by
    simp_rw [hd]
    have h := (measurePreserving_add_left (volume : Measure ℂ) b).setIntegral_image_emb
      (MeasurableEquiv.addLeft b).measurableEmbedding (diskMapEnergyDensity g u)
      {z : ℂ | ‖z‖ ∈ Icc r R}
    have heq : (fun z : ℂ => b + z) '' {z : ℂ | ‖z‖ ∈ Icc r R} =
        {z : ℂ | dist z b ∈ Icc r R} := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa only [mem_ofPred_eq, dist_eq_norm, add_sub_cancel_left] using hw
      · intro hz
        refine ⟨z - b, ?_, add_sub_cancel _ _⟩
        simpa only [mem_ofPred_eq, dist_eq_norm] using hz
    rw [heq] at h
    exact h.symm
  obtain ⟨ρ, hρ, hint, hbound⟩ :=
    exists_radius_circle_energy_le_annular_disk_energy g hU hr hrR
  have hc (s : ℝ) : circleMap 0 ρ (2 * Real.pi * s - Real.pi) =
      ρ • circleMap 0 1 (2 * Real.pi * s - Real.pi) := by
    simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.real_smul]
  have heq : (fun s => U (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) =
      fun s => u (b + ρ • circleMap 0 1 (2 * Real.pi * s - Real.pi)) := by
    funext s
    rw [hc]
  rw [heq] at hint hbound
  rw [hi] at hbound
  exact ⟨ρ, hρ, hint, hbound⟩

end DifferentialGeometry.Geometry

end

end
