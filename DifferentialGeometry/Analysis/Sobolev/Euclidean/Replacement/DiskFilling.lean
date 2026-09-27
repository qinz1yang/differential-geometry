import DifferentialGeometry.Analysis.Sobolev.Euclidean.LipschitzWitness
import DifferentialGeometry.Analysis.Sobolev.Interpolation.AnnulusEnergy
import DifferentialGeometry.Analysis.Sobolev.Interpolation.Cylinder
import DifferentialGeometry.Analysis.Integration.BallBoundary
import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import Mathlib.Analysis.Real.Pi.Bounds
import DifferentialGeometry.Analysis.Integration.PolarAnnulus
import DifferentialGeometry.Analysis.Integration.PlaneScaling
import Mathlib.MeasureTheory.Integral.Average
import DifferentialGeometry.Analysis.Integration.Lp.QuadraticDomination

noncomputable section
open Set MeasureTheory Filter
open DifferentialGeometry.Topology DifferentialGeometry.Analysis.Sobolev
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

private theorem lipschitz_circle_parameter :
    LipschitzWith ⟨2 * Real.pi, by positivity⟩
      (fun t : ℝ => circleMap 0 1 (2 * Real.pi * t - Real.pi)) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => circleMap 0 1 (2 * Real.pi * t - Real.pi))
      ((2 * Real.pi) • (circleMap 0 1 (2 * Real.pi * t - Real.pi) * Complex.I)) t := by
    have hθ : HasDerivAt (fun t : ℝ => 2 * Real.pi * t - Real.pi) (2 * Real.pi) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * Real.pi)).sub_const Real.pi
    exact (hasDerivAt_circleMap 0 1 (2 * Real.pi * t - Real.pi)).scomp t hθ
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hd t).differentiableAt)
  intro t
  change ‖deriv (fun t : ℝ => circleMap 0 1 (2 * Real.pi * t - Real.pi)) t‖ ≤ _
  rw [(hd t).deriv]
  simp [abs_of_pos Real.pi_pos]

private theorem norm_sub_start_sq_le_integral_deriv_sq
    {b : ℝ → F} {C : ℝ≥0} (hb : LipschitzWith C b)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖b t - b 0‖ ^ 2 ≤ ∫ s in Icc (0 : ℝ) 1, ‖deriv b s‖ ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hdb : MemLp (deriv b) 2 μ := MemLp.of_bound (aestronglyMeasurable_deriv b _) C
    (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hb)
  have hdi : Integrable (fun s => ‖deriv b s‖) μ := hdb.norm.integrable (by norm_num)
  have hac : AbsolutelyContinuousOnInterval b 0 t :=
    hb.lipschitzOnWith.absolutelyContinuousOnInterval
  have hnorm : ‖b t - b 0‖ ≤ ∫ s, ‖deriv b s‖ ∂μ := by
    rw [← hac.integral_deriv_eq_sub_vector]
    calc
      _ ≤ ∫ s in uIoc (0 : ℝ) t, ‖deriv b s‖ :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ s, ‖deriv b s‖ ∂μ := by
        exact setIntegral_mono_set hdi
          (Eventually.of_forall fun _ => norm_nonneg _) (by
            apply Eventually.of_forall
            intro s hs
            rw [uIoc_of_le ht.1] at hs
            exact ⟨hs.1.le, hs.2.trans ht.2⟩)
  have hholder : (∫ s, ‖deriv b s‖ ∂μ) ≤
      Real.sqrt (∫ s, ‖deriv b s‖ ^ 2 ∂μ) := by
    have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
      (f := fun _ : ℝ => (1 : ℝ)) (g := fun s => ‖deriv b s‖)
      (by simpa using (memLp_const (p := 2) (μ := μ) (1 : ℝ)))
      (by simpa using hdb.norm)
    simpa only [norm_one, norm_norm, one_mul, one_pow, integral_const, Measure.real, μ,
      Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      ENNReal.toReal_one, smul_eq_mul, Real.one_rpow, Real.rpow_two,
      ← Real.sqrt_eq_rpow, Real.sqrt_one] using h
  have hnonneg : 0 ≤ ∫ s, ‖deriv b s‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  calc
    ‖b t - b 0‖ ^ 2 ≤ (Real.sqrt (∫ s, ‖deriv b s‖ ^ 2 ∂μ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hholder) 2
    _ = _ := Real.sq_sqrt hnonneg

private theorem integral_norm_sub_start_sq_le_integral_deriv_sq
    {b : ℝ → F} {C : ℝ≥0} (hb : LipschitzWith C b) :
    (∫ t in Icc (0 : ℝ) 1, ‖b t - b 0‖ ^ 2) ≤
      ∫ s in Icc (0 : ℝ) 1, ‖deriv b s‖ ^ 2 := by
  have hv : IntegrableOn (fun t => ‖b t - b 0‖ ^ 2) (Icc (0 : ℝ) 1) :=
    ((hb.continuous.sub continuous_const).norm.pow 2).integrableOn_Icc
  have h := setIntegral_mono_on hv
    (integrableOn_const (by simp : volume (Icc (0 : ℝ) 1) ≠ ∞)) measurableSet_Icc
    (fun t ht => norm_sub_start_sq_le_integral_deriv_sq hb ht)
  simpa only [setIntegral_const, Measure.real, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one, ENNReal.toReal_one, one_smul] using h


private theorem integrableOn_plane_energy_of_lipschitz {f : ℂ → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) (R : ℝ) :
    IntegrableOn (fun z => (‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2)
      (Metric.closedBall (0 : ℂ) R) := by
  borelize F
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne
  have hm (v : ℂ) : MemLp (fun z => fderiv ℝ f z v) 2
      (volume.restrict (Metric.closedBall (0 : ℂ) R)) :=
    MemLp.of_bound (measurable_fderiv_apply_const ℝ f v).aestronglyMeasurable
      ((C : ℝ) * ‖v‖) (Eventually.of_forall fun z =>
        ((fderiv ℝ f z).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v)))
  exact ((hm 1).norm.integrable_sq.add (hm Complex.I).norm.integrable_sq).div_const 2

private theorem integral_plane_energy_constant_cap
    (u : ℂ → F) (p : F) (T : F → F) {C : ℝ≥0}
    (hf : LipschitzWith C (attachThinAnnulus u (fun _ => p) T 1 (1 / 2))) :
    (∫ z in Metric.closedBall (0 : ℂ) 1,
      (‖fderiv ℝ (attachThinAnnulus u (fun _ => p) T 1 (1 / 2)) z 1‖ ^ 2 +
        ‖fderiv ℝ (attachThinAnnulus u (fun _ => p) T 1 (1 / 2)) z Complex.I‖ ^ 2) / 2) ≤
      ∫ z in {z : ℂ | ‖z‖ ∈ Icc (1 / 2 : ℝ) 1},
        (‖fderiv ℝ (attachThinAnnulus u (fun _ => p) T 1 (1 / 2)) z 1‖ ^ 2 +
          ‖fderiv ℝ (attachThinAnnulus u (fun _ => p) T 1 (1 / 2)) z Complex.I‖ ^ 2) / 2 := by
  let f := attachThinAnnulus u (fun _ => p) T 1 (1 / 2)
  let e := fun z => (‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2
  have hi : IntegrableOn e (Metric.closedBall (0 : ℂ) 1) :=
    integrableOn_plane_energy_of_lipschitz hf 1
  have hsub : Metric.closedBall (0 : ℂ) (1 / 2) ⊆ Metric.closedBall (0 : ℂ) 1 :=
    Metric.closedBall_subset_closedBall (by norm_num)
  have hzero : (∫ z in Metric.closedBall (0 : ℂ) (1 / 2), e z) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_mem_ball_of_measure_sphere_eq_zero
      (Measure.addHaar_sphere volume (0 : ℂ) (1 / 2))] with z hz
    have heq : f =ᶠ[𝓝 z] (fun _ => p) :=
      attachThinAnnulus_eventuallyEq_inner u (fun _ => p) T 1 (1 / 2)
        (by
          have hh : ‖z‖ < 1/2 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
          linarith)
    simp only [e, heq.fderiv_eq, fderiv_const_apply, zero_apply,
      norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, zero_div, Pi.zero_apply]
  have hsplit := setIntegral_sdiff measurableSet_closedBall hi hsub
  rw [hzero, sub_zero] at hsplit
  change (∫ z in Metric.closedBall (0 : ℂ) 1, e z) ≤ _
  rw [← hsplit]
  have hAnnSub : {z : ℂ | ‖z‖ ∈ Icc (1 / 2 : ℝ) 1} ⊆ Metric.closedBall (0 : ℂ) 1 :=
    fun z hz => Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hz.2)
  apply setIntegral_mono_set (hi.mono_set hAnnSub)
    (Eventually.of_forall fun z => by dsimp [e]; positivity)
  apply Filter.Eventually.of_forall
  intro z hz
  exact ⟨le_of_lt (lt_of_not_ge (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2)),
    by simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1⟩

theorem exists_lipschitz_retracted_disk_filling_energy_le
    {u : ℂ → F} {C : ℝ≥0} (hu : LipschitzWith C u) (p : F)
    {K U : Set F} (hp : p ∈ K)
    (huK : ∀ z : ℂ, ‖z‖ = 1 → u z ∈ K)
    (hsegments : ∀ z : ℂ, ‖z‖ = 1 → segment ℝ p (u z) ⊆ U)
    (T : F → F) (hT : Differentiable ℝ T) {L : ℝ}
    (hL : ∀ x, ‖fderiv ℝ T x‖ ≤ L) (hTK : MapsTo T U K)
    (hfix : ∀ y ∈ K, T y = y) :
    ∃ f : ℂ → F, (∃ C' : ℝ≥0, LipschitzWith C' f) ∧
      (∀ z, 1 ≤ ‖z‖ → f z = u z) ∧
      (∀ z, ‖z‖ ≤ 1 / 2 → f z = p) ∧
      MapsTo f (Metric.closedBall (0 : ℂ) 1) K ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1,
        (‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2) ≤
        (2 * Real.pi) * max 1 (((2 * Real.pi) ^ 2 * (1 / 2))⁻¹) * L ^ 2 *
          ((∫ t in Icc (0 : ℝ) 1,
            ‖u (circleMap 0 1 (2 * Real.pi * t - Real.pi)) - p‖ ^ 2) +
            (1 / 4) * ∫ t in Icc (0 : ℝ) 1,
              ‖deriv (fun s => u (circleMap 0 1 (2 * Real.pi * s - Real.pi))) t‖ ^ 2) := by
  have hLp : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hTl : LipschitzWith ⟨L, hLp⟩ T := lipschitzWith_of_nnnorm_fderiv_le hT hL
  have hconst : LipschitzWith 0 (fun _ : ℂ => p) := LipschitzWith.const p
  have hTu : ∀ z : ℂ, ‖z‖ = 1 → T (u z) = u z := fun z hz => hfix _ (huK z hz)
  have hTp : ∀ z : ℂ, ‖z‖ = 1 → T p = p := fun _ _ => hfix _ hp
  obtain ⟨C', hf⟩ := attachThinAnnulus_lipschitz (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hu hconst hTl hTu hTp
  let f := attachThinAnnulus u (fun _ => p) T 1 (1 / 2)
  refine ⟨f, ⟨C', hf⟩, (fun z hz => attachThinAnnulus_outer _ _ _ (by norm_num) hz), ?_, ?_, ?_⟩
  · intro z hz
    exact attachThinAnnulus_inner _ _ _ _ _ (by linarith)
  · intro z hz
    by_cases hi : ‖z‖ ≤ 1 / 2
    · rw [show f z = p from attachThinAnnulus_inner _ _ _ _ _ (by linarith)]
      exact hp
    · have hzo : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      change attachThinAnnulus u (fun _ => p) T 1 (1/2) z ∈ K
      rw [attachThinAnnulus_shell u (fun _ => p) T (by norm_num : (0 : ℝ) < 1/2)
        (by norm_num : (1/2 : ℝ) < 1) hTu hTp ⟨by linarith [lt_of_not_ge hi], hzo⟩]
      apply hTK
      have hθ := thinAnnulusParameter_mem_Icc (by norm_num : (0 : ℝ) < 1/2)
        (show 1 - 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 from ⟨by linarith [lt_of_not_ge hi], hzo⟩)
      apply hsegments _ (thinAnnulusProjection_norm (by norm_num) z)
      simpa only [thinAnnulusInterpolation, AffineMap.lineMap_apply_module] using
        (lineMap_mem_segment ℝ p (u (thinAnnulusProjection 1 z)) hθ)
  · have ha : LipschitzWith 0 (fun _ : ℝ => p) := LipschitzWith.const p
    have hb : LipschitzWith (C * ⟨2 * Real.pi, by positivity⟩)
        (fun t : ℝ => u (circleMap 0 1 (2 * Real.pi * t - Real.pi))) :=
      hu.comp lipschitz_circle_parameter
    have hAnn := integral_annulus_energy_attachThinAnnulus_le_of_lipschitz
      (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
      hu hconst hTl hTu hTp
    have hComp := integral_energy_comp_affineCylinderInterpolation_le (1/2 : ℝ)
      ha hb T hT hL
    have hCyl := integral_energy_affineCylinderInterpolation_le
      (by norm_num : (0 : ℝ) < 1/2) ha hb
    have hCyl' : (∫ q in Icc (0 : ℝ) (1/2) ×ˢ Icc (0 : ℝ) 1,
        (‖fderiv ℝ (affineCylinderInterpolation (1/2) (fun _ => p)
            (fun t => u (circleMap 0 1 (2 * Real.pi * t - Real.pi)))) q (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (affineCylinderInterpolation (1/2) (fun _ => p)
            (fun t => u (circleMap 0 1 (2 * Real.pi * t - Real.pi)))) q (0, 1)‖ ^ 2) / 2) ≤
        (∫ t in Icc (0 : ℝ) 1, ‖u (circleMap 0 1 (2 * Real.pi * t - Real.pi)) - p‖ ^ 2) +
          (1/4) * ∫ t in Icc (0 : ℝ) 1,
            ‖deriv (fun s => u (circleMap 0 1 (2 * Real.pi * s - Real.pi))) t‖ ^ 2 := by
      simpa only [deriv_const, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
        norm_sub_rev, show (1 / (2 * (1/2)) : ℝ) = 1 by norm_num,
        show ((1/2) / 2 : ℝ) = 1/4 by norm_num, one_mul] using hCyl
    have hAnn' := hAnn.trans (mul_le_mul_of_nonneg_left
      (hComp.trans (mul_le_mul_of_nonneg_left hCyl' (sq_nonneg L)))
      (show 0 ≤ (2 * Real.pi) * max 1 (((2 * Real.pi) ^ 2 * (1 - 1/2))⁻¹) by positivity))
    have hwhole := integral_plane_energy_constant_cap u p T hf
    norm_num only [show (1 : ℝ) - 1/2 = 1/2 by norm_num] at hAnn'
    simpa only [mul_assoc] using hwhole.trans hAnn'

private theorem exists_unit_circle_parameter {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ t ∈ Icc (0 : ℝ) 1, circleMap 0 1 (2 * Real.pi * t - Real.pi) = z := by
  have hmem : z ∈ range (circleMap 0 1) := by
    rw [range_circleMap, Metric.mem_sphere, dist_zero_right]
    simpa using hz
  rw [← (periodic_circleMap 0 1).image_Ioc Real.two_pi_pos (-Real.pi)] at hmem
  obtain ⟨θ, hθ, hθz⟩ := hmem
  refine ⟨(θ + Real.pi) / (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
  · exact div_nonneg (by linarith [hθ.1]) (by positivity)
  · exact (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr (by linarith [hθ.2])
  · have heq : 2 * Real.pi * ((θ + Real.pi) / (2 * Real.pi)) - Real.pi = θ := by
      field_simp
      ring
    rwa [heq]

theorem exists_lipschitz_retracted_disk_filling_of_small_boundary_energy
    {u : ℂ → F} {C : ℝ≥0} (hu : LipschitzWith C u) (p : F)
    (hanchor : u (circleMap 0 1 (-Real.pi)) = p)
    {K U : Set F} (huK : ∀ z : ℂ, ‖z‖ = 1 → u z ∈ K)
    {η : ℝ} (hη : 0 < η) (hball : Metric.ball p η ⊆ U)
    (hsmall : (∫ t in Icc (0 : ℝ) 1,
      ‖deriv (fun s => u (circleMap 0 1 (2 * Real.pi * s - Real.pi))) t‖ ^ 2) < η ^ 2)
    (T : F → F) (hT : Differentiable ℝ T) {L : ℝ}
    (hL : ∀ x, ‖fderiv ℝ T x‖ ≤ L) (hTK : MapsTo T U K)
    (hfix : ∀ y ∈ K, T y = y) :
    ∃ f : ℂ → F, (∃ C' : ℝ≥0, LipschitzWith C' f) ∧
      (∀ z, 1 ≤ ‖z‖ → f z = u z) ∧
      (∀ z, ‖z‖ ≤ 1 / 2 → f z = p) ∧
      MapsTo f (Metric.closedBall (0 : ℂ) 1) K ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1,
        (‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2) ≤
        (5 * Real.pi / 2) * L ^ 2 * ∫ t in Icc (0 : ℝ) 1,
          ‖deriv (fun s => u (circleMap 0 1 (2 * Real.pi * s - Real.pi))) t‖ ^ 2 := by
  let b := fun t : ℝ => u (circleMap 0 1 (2 * Real.pi * t - Real.pi))
  have hb : LipschitzWith (C * ⟨2 * Real.pi, by positivity⟩) b :=
    hu.comp lipschitz_circle_parameter
  have hb0 : b 0 = p := by simpa only [b, mul_zero, zero_sub] using hanchor
  have hp : p ∈ K := by
    rw [← hanchor]
    exact huK _ (by simp)
  have hnear : ∀ z : ℂ, ‖z‖ = 1 → u z ∈ Metric.ball p η := by
    intro z hz
    obtain ⟨t, ht, htz⟩ := exists_unit_circle_parameter hz
    have he := norm_sub_start_sq_le_integral_deriv_sq hb ht
    rw [hb0] at he
    have hzmem : ‖b t - p‖ < η := by
      have he' : ‖b t - p‖ ^ 2 < η ^ 2 := he.trans_lt hsmall
      nlinarith [norm_nonneg (b t - p)]
    simpa only [b, htz, Metric.mem_ball, dist_eq_norm] using hzmem
  have hseg : ∀ z : ℂ, ‖z‖ = 1 → segment ℝ p (u z) ⊆ U := by
    intro z hz
    exact ((convex_ball p η).segment_subset (Metric.mem_ball_self hη) (hnear z hz)).trans hball
  obtain ⟨f, hf, htrace, hconst, htarget, henergy⟩ :=
    exists_lipschitz_retracted_disk_filling_energy_le hu p hp huK hseg T hT hL hTK hfix
  refine ⟨f, hf, htrace, hconst, htarget, ?_⟩
  have hgap := integral_norm_sub_start_sq_le_integral_deriv_sq hb
  rw [hb0] at hgap
  have hmax : max (1 : ℝ) (((2 * Real.pi) ^ 2 * (1/2))⁻¹) = 1 := by
    apply max_eq_left
    apply inv_le_one_of_one_le₀
    nlinarith [Real.pi_gt_three]
  rw [hmax, mul_one] at henergy
  have hcoef : 0 ≤ (2 * Real.pi) * L ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
  apply henergy.trans
  calc
    _ ≤ (2 * Real.pi) * L ^ 2 *
        ((∫ t in Icc (0 : ℝ) 1, ‖deriv b t‖ ^ 2) +
          (1/4) * ∫ t in Icc (0 : ℝ) 1, ‖deriv b t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hgap le_rfl) hcoef
    _ = _ := by ring


section Sobolev

variable {ι : Type*} [Fintype ι]

private theorem coordinate_witnesses_on_unit_ball_of_lipschitz
    {f : ℂ → EuclideanSpace ℝ ι} {C : ℝ≥0} (hf : LipschitzWith C f) :
    ∃ hw : ∀ i : ι, DeGiorgi.MemW1pWitness 2
        (fun x : EuclideanSpace ℝ (Fin 2) =>
          f (Complex.orthonormalBasisOneI.repr.symm x) i)
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1),
      ∀ i x j, (hw i).weakGrad x j =
        fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
          f (Complex.orthonormalBasisOneI.repr.symm y) i) x (EuclideanSpace.single j 1) := by
  let g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι :=
    fun x => f (Complex.orthonormalBasisOneI.repr.symm x)
  have hg : LipschitzWith C g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (f (Complex.orthonormalBasisOneI.repr.symm x))
      (f (Complex.orthonormalBasisOneI.repr.symm y)) ≤ (C : ℝ) * dist x y
    exact (hf.dist_le_mul _ _).trans_eq
      (congrArg (fun z : ℝ => (C : ℝ) * z)
        (Complex.orthonormalBasisOneI.repr.symm.isometry.dist_eq x y))
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) :=
    isFiniteMeasure_restrict.mpr
      ((measure_mono Metric.ball_subset_closedBall).trans_lt
        (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).measure_lt_top).ne
  have hgm : MemLp g 2 (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) := by
    obtain ⟨B, hB⟩ :=
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).exists_bound_of_continuousOn
        hg.continuous.continuousOn
    apply MemLp.of_bound hg.continuous.aestronglyMeasurable B
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hB x (Metric.ball_subset_closedBall hx)
  have hgd : MemLp (fderiv ℝ g) 2
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) := by
    apply MemLp.of_bound (measurable_fderiv ℝ g).aestronglyMeasurable C
    exact Eventually.of_forall fun x => norm_fderiv_le_of_lipschitz ℝ hg
  obtain ⟨hw, hrep, _⟩ := Sobolev.Euclidean.exists_coordinate_memW1pWitness_fderiv_of_lipschitz
    hg hgm hgd
  exact ⟨hw, hrep⟩

theorem exists_memW1p_retracted_disk_filling_of_small_boundary_energy
    {u : ℂ → EuclideanSpace ℝ ι} {C : ℝ≥0} (hu : LipschitzWith C u)
    (p : EuclideanSpace ℝ ι) (hanchor : u (circleMap 0 1 (-Real.pi)) = p)
    {K U : Set (EuclideanSpace ℝ ι)} (huK : ∀ z : ℂ, ‖z‖ = 1 → u z ∈ K)
    {η : ℝ} (hη : 0 < η) (hball : Metric.ball p η ⊆ U)
    (hsmall : (∫ t in Icc (0 : ℝ) 1,
      ‖deriv (fun s => u (circleMap 0 1 (2 * Real.pi * s - Real.pi))) t‖ ^ 2) < η ^ 2)
    (T : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (hT : Differentiable ℝ T) {L : ℝ}
    (hL : ∀ x, ‖fderiv ℝ T x‖ ≤ L) (hTK : MapsTo T U K)
    (hfix : ∀ y ∈ K, T y = y) :
    ∃ f : ℂ → EuclideanSpace ℝ ι, (∃ C' : ℝ≥0, LipschitzWith C' f) ∧
      (∀ z, 1 ≤ ‖z‖ → f z = u z) ∧
      (∀ z, ‖z‖ ≤ 1 / 2 → f z = p) ∧
      MapsTo f (Metric.closedBall (0 : ℂ) 1) K ∧
      (∃ hw : ∀ i : ι, DeGiorgi.MemW1pWitness 2
        (fun x : EuclideanSpace ℝ (Fin 2) =>
          f (Complex.orthonormalBasisOneI.repr.symm x) i)
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1),
        ∀ i x j, (hw i).weakGrad x j =
          fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
            f (Complex.orthonormalBasisOneI.repr.symm y) i) x (EuclideanSpace.single j 1)) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1,
        (‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2) ≤
        (5 * Real.pi / 2) * L ^ 2 * ∫ t in Icc (0 : ℝ) 1,
          ‖deriv (fun s => u (circleMap 0 1 (2 * Real.pi * s - Real.pi))) t‖ ^ 2 := by
  obtain ⟨f, hf, htrace, hconst, htarget, henergy⟩ :=
    exists_lipschitz_retracted_disk_filling_of_small_boundary_energy hu p hanchor huK
      hη hball hsmall T hT hL hTK hfix
  exact ⟨f, hf, htrace, hconst, htarget,
    coordinate_witnesses_on_unit_ball_of_lipschitz hf.choose_spec, henergy⟩

end Sobolev

end DifferentialGeometry.Analysis

end

noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

private theorem smul_circleMap_unit (ρ θ : ℝ) :
    ρ • circleMap 0 1 θ = circleMap 0 ρ θ := by
  simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.real_smul]

omit [FiniteDimensional ℝ F] in
private theorem integral_plane_energy_scale {f : ℂ → F} {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ z in Metric.closedBall (0 : ℂ) ρ,
      (‖fderiv ℝ (fun w => f (ρ⁻¹ • w)) z 1‖ ^ 2 +
        ‖fderiv ℝ (fun w => f (ρ⁻¹ • w)) z Complex.I‖ ^ 2) / 2) =
      ∫ z in Metric.closedBall (0 : ℂ) 1,
        (‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2 := by
  have h := integral_quadratic_fderiv_comp_smul_closedBall
    (fun _ : F => innerSL ℝ) f hρ (by norm_num : (0 : ℝ) < 1)
  have he (v : F) : (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) v v = ‖v‖ ^ 2 :=
    real_inner_self_eq_norm_sq v
  simpa only [one_div, he] using h

theorem exists_lipschitz_retracted_disk_filling_at_radius
    {u : ℂ → F} {C : ℝ≥0} (hu : LipschitzWith C u) {ρ : ℝ} (hρ : 0 < ρ)
    (p : F) (hanchor : u (circleMap 0 ρ (-Real.pi)) = p)
    {K U : Set F} (huK : ∀ z : ℂ, ‖z‖ = ρ → u z ∈ K)
    {η : ℝ} (hη : 0 < η) (hball : Metric.ball p η ⊆ U)
    (hsmall : (∫ t in Icc (0 : ℝ) 1,
      ‖deriv (fun s => u (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t‖ ^ 2) < η ^ 2)
    (T : F → F) (hT : Differentiable ℝ T) {L : ℝ}
    (hL : ∀ x, ‖fderiv ℝ T x‖ ≤ L) (hTK : MapsTo T U K)
    (hfix : ∀ y ∈ K, T y = y) :
    ∃ f : ℂ → F, (∃ C' : ℝ≥0, LipschitzWith C' f) ∧
      (∀ z, ρ ≤ ‖z‖ → f z = u z) ∧
      (∀ z, ‖z‖ ≤ ρ / 2 → f z = p) ∧
      MapsTo f (Metric.closedBall (0 : ℂ) ρ) K ∧
      (∫ z in Metric.closedBall (0 : ℂ) ρ,
        (‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2) ≤
        (5 * Real.pi / 2) * L ^ 2 * ∫ t in Icc (0 : ℝ) 1,
          ‖deriv (fun s => u (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t‖ ^ 2 := by
  let v := fun z : ℂ => u (ρ • z)
  have hv : LipschitzWith (C * ‖ρ‖₊) v := hu.comp (lipschitzWith_smul ρ)
  have hanchor' : v (circleMap 0 1 (-Real.pi)) = p := by
    dsimp only [v]
    rwa [smul_circleMap_unit]
  have hvK : ∀ z : ℂ, ‖z‖ = 1 → v z ∈ K := by
    intro z hz
    exact huK _ (by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, hz, mul_one])
  have hcircle : (fun s => v (circleMap 0 1 (2 * Real.pi * s - Real.pi))) =
      (fun s => u (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) := by
    funext s
    exact congrArg u (smul_circleMap_unit ρ _)
  obtain ⟨f, ⟨Cf, hf⟩, htrace, hconst, htarget, henergy⟩ :=
    exists_lipschitz_retracted_disk_filling_of_small_boundary_energy hv p hanchor' hvK hη hball
      (by rwa [hcircle]) T hT hL hTK hfix
  refine ⟨fun z => f (ρ⁻¹ • z),
    ⟨Cf * ‖ρ⁻¹‖₊, hf.comp (lipschitzWith_smul ρ⁻¹)⟩, ?_, ?_, ?_, ?_⟩
  · intro z hz
    dsimp only
    have hn : 1 ≤ ‖ρ⁻¹ • z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
      exact (one_le_div hρ).mpr hz |>.trans_eq (by rw [div_eq_inv_mul])
    rw [htrace _ hn]
    dsimp only [v]
    rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
  · intro z hz
    apply hconst
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
    have hn := mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hρ.le)
    calc ρ⁻¹ * ‖z‖ ≤ ρ⁻¹ * (ρ / 2) := hn
      _ = 1 / 2 := by field_simp
  · intro z hz
    apply htarget
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
    have hz' : ‖z‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact (mul_le_mul_of_nonneg_left hz' (inv_nonneg.mpr hρ.le)).trans_eq
      (inv_mul_cancel₀ hρ.ne')
  · rw [integral_plane_energy_scale hρ]
    rwa [hcircle] at henergy

theorem exists_radius_retracted_filling_energy_le_annulus
    {u : ℂ → F} {C : ℝ≥0} (hu : LipschitzWith C u) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    {K U : Set F} (huK : MapsTo u (Metric.closedBall (0 : ℂ) R) K)
    {η : ℝ} (hη : 0 < η) (htube : ∀ p ∈ K, Metric.ball p η ⊆ U)
    (hsmall : (2 * Real.pi * R / (R - r)) *
      (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖fderiv ℝ u z‖ ^ 2) < η ^ 2)
    (T : F → F) (hT : Differentiable ℝ T) {L : ℝ}
    (hL : ∀ x, ‖fderiv ℝ T x‖ ≤ L) (hTK : MapsTo T U K)
    (hfix : ∀ y ∈ K, T y = y) :
    ∃ ρ ∈ Icc r R, ∃ f : ℂ → F, (∃ C' : ℝ≥0, LipschitzWith C' f) ∧
      (∀ z, ρ ≤ ‖z‖ → f z = u z) ∧
      (∀ z, ‖z‖ ≤ ρ / 2 → f z = u (circleMap 0 ρ (-Real.pi))) ∧
      MapsTo f (Metric.closedBall (0 : ℂ) R) K ∧
      (∫ z in Metric.closedBall (0 : ℂ) ρ,
        (‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2) ≤
        (5 * Real.pi ^ 2 * R / (R - r)) * L ^ 2 *
          ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖fderiv ℝ u z‖ ^ 2 := by
  let D := fun ρ => ∫ t in Icc (0 : ℝ) 1,
    ‖deriv (fun s => u (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t‖ ^ 2
  let μ := volume.restrict (Icc r R)
  have hi : Integrable D μ := integrableOn_integral_norm_sq_deriv_circleMap hu hr hrR.le
  have hμ : μ ≠ 0 := by
    intro hzero
    have hz := congrArg (fun m : Measure ℝ => m univ) hzero
    have hpos : 0 < volume (Icc r R) := by simp [Real.volume_Icc, hrR]
    exact hpos.ne' (by
      simpa only [μ, Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using hz)
  have hnull : μ (Icc r R)ᶜ = 0 := by simp [μ]
  obtain ⟨ρ, hρ, hρD⟩ := exists_notMem_null_le_average hμ hi hnull
  have hρcc : ρ ∈ Icc r R := by simpa only [mem_compl_iff, not_not] using hρ
  have hmean : (⨍ t, D t ∂μ) = (R - r)⁻¹ * ∫ t, D t ∂μ := by
    rw [average_eq, smul_eq_mul]
    congr 1
    simp only [μ, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hrR.le)]
  have hD : D ρ ≤ (2 * Real.pi * R / (R - r)) *
      (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖fderiv ℝ u z‖ ^ 2) := by
    rw [hmean] at hρD
    exact hρD.trans ((mul_le_mul_of_nonneg_left
      (integral_norm_sq_deriv_circleMap_radial_le hu hr hrR.le)
      (inv_nonneg.mpr (sub_nonneg.mpr hrR.le))).trans_eq (by ring))
  have hρ0 : 0 < ρ := hr.trans_le hρcc.1
  have hKρ : ∀ z : ℂ, ‖z‖ = ρ → u z ∈ K := fun z hz => huK
    (Metric.mem_closedBall.mpr (by simpa only [dist_zero_right, hz] using hρcc.2))
  have hp := hKρ (circleMap 0 ρ (-Real.pi)) (by simp [abs_of_pos hρ0])
  obtain ⟨f, hf, htrace, hconst, htarget, henergy⟩ :=
    exists_lipschitz_retracted_disk_filling_at_radius hu hρ0 _ rfl hKρ hη (htube _ hp)
      (hD.trans_lt hsmall) T hT hL hTK hfix
  refine ⟨ρ, hρcc, f, hf, htrace, hconst, ?_, ?_⟩
  · intro z hz
    by_cases hn : ‖z‖ ≤ ρ
    · exact htarget (Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hn))
    · rw [htrace z (lt_of_not_ge hn).le]
      exact huK hz
  · apply henergy.trans
    have hcoef : 0 ≤ (5 * Real.pi / 2) * L ^ 2 := by positivity
    exact (mul_le_mul_of_nonneg_left hD hcoef).trans_eq (by ring)

end DifferentialGeometry.Analysis

end

noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem complex_opNorm_sq_le_four_column_energy (A : ℂ →L[ℝ] F) :
    ‖A‖ ^ 2 ≤ 4 * ((‖A 1‖ ^ 2 + ‖A Complex.I‖ ^ 2) / 2) := by
  have hn : ‖A‖ ≤ ‖A 1‖ + ‖A Complex.I‖ := by
    apply A.opNorm_le_bound (add_nonneg (norm_nonneg _) (norm_nonneg _))
    intro z
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      simp only [Complex.real_smul, mul_one]
      exact z.re_add_im.symm
    calc
      ‖A z‖ = ‖z.re • A 1 + z.im • A Complex.I‖ := by
        conv_lhs => rw [hz, map_add, map_smul, map_smul]
      _ ≤ ‖z.re • A 1‖ + ‖z.im • A Complex.I‖ := norm_add_le _ _
      _ = |z.re| * ‖A 1‖ + |z.im| * ‖A Complex.I‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖z‖ * ‖A 1‖ + ‖z‖ * ‖A Complex.I‖ := by
        gcongr
        · exact Complex.abs_re_le_norm z
        · exact Complex.abs_im_le_norm z
      _ = (‖A 1‖ + ‖A Complex.I‖) * ‖z‖ := by ring
  have hs := pow_le_pow_left₀ (norm_nonneg A) hn 2
  nlinarith [sq_nonneg (‖A 1‖ - ‖A Complex.I‖)]

private theorem column_energy_le_complex_opNorm_sq (A : ℂ →L[ℝ] F) :
    (‖A 1‖ ^ 2 + ‖A Complex.I‖ ^ 2) / 2 ≤ ‖A‖ ^ 2 := by
  have h₁ : ‖A 1‖ ≤ ‖A‖ := by simpa only [norm_one, mul_one] using A.le_opNorm 1
  have h₂ : ‖A Complex.I‖ ≤ ‖A‖ := by
    simpa only [Complex.norm_I, mul_one] using A.le_opNorm Complex.I
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) h₁ 2, pow_le_pow_left₀ (norm_nonneg _) h₂ 2]

variable [FiniteDimensional ℝ F]

private theorem integrableOn_fderiv_sq_of_lipschitz {f : ℂ → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) (Q : ℝ) :
    IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) (Metric.closedBall (0 : ℂ) Q) := by
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) Q)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) Q).measure_lt_top.ne
  have hm : MemLp (fderiv ℝ f) 2 (volume.restrict (Metric.closedBall (0 : ℂ) Q)) :=
    MemLp.of_bound (measurable_fderiv ℝ f).aestronglyMeasurable C
      (Eventually.of_forall fun _ => norm_fderiv_le_of_lipschitz ℝ hf)
  exact hm.norm.integrable_sq

private theorem integrableOn_column_energy_of_lipschitz {f : ℂ → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) (Q : ℝ) :
    IntegrableOn (fun z => (‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2)
      (Metric.closedBall (0 : ℂ) Q) := by
  borelize F
  have hm := (((measurable_fderiv_apply_const ℝ f 1).norm.pow_const 2).add
    ((measurable_fderiv_apply_const ℝ f Complex.I).norm.pow_const 2)).div_const 2
  apply (integrableOn_fderiv_sq_of_lipschitz hf Q).mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro z
  change ‖(‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2‖ ≤ _
  rw [Real.norm_of_nonneg (by positivity)]
  exact column_energy_le_complex_opNorm_sq _

theorem integral_fderiv_sq_le_of_exterior_eq_of_filling_energy_bound
    {f u : ℂ → F} {Cf Cu : ℝ≥0} (hf : LipschitzWith Cf f) (hu : LipschitzWith Cu u)
    {ρ Q : ℝ} (hρQ : ρ ≤ Q) (hfix : ∀ z, ρ ≤ ‖z‖ → f z = u z)
    {B : ℝ} (hfill : (∫ z in Metric.closedBall (0 : ℂ) ρ,
      (‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2) ≤ B) :
    (∫ z in Metric.closedBall (0 : ℂ) Q, ‖fderiv ℝ f z‖ ^ 2) ≤
      4 * (B + ∫ z in Metric.closedBall (0 : ℂ) Q, ‖fderiv ℝ u z‖ ^ 2) := by
  let ef := fun z => (‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2
  let eu := fun z => (‖fderiv ℝ u z 1‖ ^ 2 + ‖fderiv ℝ u z Complex.I‖ ^ 2) / 2
  have hif : IntegrableOn ef (Metric.closedBall (0 : ℂ) Q) :=
    integrableOn_column_energy_of_lipschitz hf Q
  have hiu : IntegrableOn eu (Metric.closedBall (0 : ℂ) Q) :=
    integrableOn_column_energy_of_lipschitz hu Q
  have hext : (∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall 0 ρ, ef z) =
      ∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall 0 ρ, eu z := by
    apply setIntegral_congr_fun (measurableSet_closedBall.diff measurableSet_closedBall)
    intro z hz
    have hn : ρ < ‖z‖ := lt_of_not_ge (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2)
    have heq : f =ᶠ[𝓝 z] u := by
      have hnear := (continuous_norm.tendsto z) (isOpen_Ioi.mem_nhds hn)
      filter_upwards [hnear] with w hw
      exact hfix w hw.le
    dsimp only [ef, eu]
    rw [heq.fderiv_eq]
  have hsplit := setIntegral_sdiff measurableSet_closedBall hif
    (Metric.closedBall_subset_closedBall hρQ)
  rw [hext] at hsplit
  have houter : (∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall 0 ρ, eu z) ≤
      ∫ z in Metric.closedBall (0 : ℂ) Q, eu z :=
    setIntegral_mono_set hiu (Eventually.of_forall fun z => by dsimp [eu]; positivity)
      (Eventually.of_forall fun _ hz => hz.1)
  have hsum : (∫ z in Metric.closedBall (0 : ℂ) Q, ef z) ≤
      B + ∫ z in Metric.closedBall (0 : ℂ) Q, eu z := by linarith
  have huop : (∫ z in Metric.closedBall (0 : ℂ) Q, eu z) ≤
      ∫ z in Metric.closedBall (0 : ℂ) Q, ‖fderiv ℝ u z‖ ^ 2 :=
    integral_mono_ae hiu (integrableOn_fderiv_sq_of_lipschitz hu Q)
      (Eventually.of_forall fun z => column_energy_le_complex_opNorm_sq _)
  have hfop : (∫ z in Metric.closedBall (0 : ℂ) Q, ‖fderiv ℝ f z‖ ^ 2) ≤
      4 * ∫ z in Metric.closedBall (0 : ℂ) Q, ef z := by
    rw [← integral_const_mul]
    exact integral_mono_ae (integrableOn_fderiv_sq_of_lipschitz hf Q) (hif.const_mul 4)
      (Eventually.of_forall fun z => complex_opNorm_sq_le_four_column_energy _)
  linarith

end DifferentialGeometry.Analysis

end

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private def targetPlaneEnergyDensity (A : F → F →L[ℝ] F →L[ℝ] ℝ) (f : ℂ → F) (z : ℂ) : ℝ :=
  (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
    A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2

private theorem memLp_fderiv_column_of_lipschitz {f : ℂ → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) {Q : ℝ} (v : ℂ) :
    MemLp (fun z => fderiv ℝ f z v) 2 (volume.restrict (Metric.closedBall (0 : ℂ) Q)) := by
  borelize F
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) Q)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) Q).measure_lt_top.ne
  apply MemLp.of_bound (measurable_fderiv_apply_const ℝ f v).aestronglyMeasurable
    ((C : ℝ) * ‖v‖)
  exact Eventually.of_forall fun z => ((fderiv ℝ f z).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v))

private theorem integrable_target_plane_energy
    {f : ℂ → F} {C : ℝ≥0} (hf : LipschitzWith C f)
    {K : Set F} (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K)
    {Q Λ : ℝ} (hfK : MapsTo f (Metric.closedBall (0 : ℂ) Q) K)
    (hΛ : ∀ y ∈ K, ‖A y‖ ≤ Λ) :
    IntegrableOn (targetPlaneEnergyDensity A f) (Metric.closedBall (0 : ℂ) Q) := by
  have hm : AEStronglyMeasurable (fun z => A (f z))
      (volume.restrict (Metric.closedBall (0 : ℂ) Q)) :=
    (hA.comp hf.continuous.continuousOn hfK).aestronglyMeasurable measurableSet_closedBall
  have hb : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) Q), ‖A (f z)‖ ≤ Λ := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    exact hΛ _ (hfK hz)
  have hi (v : ℂ) := integrable_bilinear_of_apply_aestronglyMeasurable
    (fun z => A (f z))
    (fun a b => (hm.apply_continuousLinearMap a).apply_continuousLinearMap b) hb
    (memLp_fderiv_column_of_lipschitz hf v) (memLp_fderiv_column_of_lipschitz hf v)
  exact ((hi 1).add (hi Complex.I)).div_const 2

theorem integral_target_energy_le_of_exterior_eq_of_filling_bound
    {f u : ℂ → F} {Cf Cu : ℝ≥0} (hf : LipschitzWith Cf f) (hu : LipschitzWith Cu u)
    {K : Set F} (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K)
    (hpos : ∀ y ∈ K, ∀ v, 0 ≤ A y v v)
    {Λ r ρ Q B : ℝ} (hΛ : ∀ y ∈ K, ‖A y‖ ≤ Λ) (hΛ0 : 0 ≤ Λ)
    (hrρ : r ≤ ρ) (hρQ : ρ ≤ Q)
    (hfK : MapsTo f (Metric.closedBall (0 : ℂ) Q) K)
    (huK : MapsTo u (Metric.closedBall (0 : ℂ) Q) K)
    (hfix : ∀ z, ρ ≤ ‖z‖ → f z = u z)
    (hfill : (∫ z in Metric.closedBall (0 : ℂ) ρ,
      (‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2) ≤ B) :
    (∫ z in Metric.closedBall (0 : ℂ) Q,
      (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
        A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2) ≤
      Λ * B + ∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall 0 r,
        (A (u z) (fderiv ℝ u z 1) (fderiv ℝ u z 1) +
          A (u z) (fderiv ℝ u z Complex.I) (fderiv ℝ u z Complex.I)) / 2 := by
  let ef := targetPlaneEnergyDensity A f
  let eu := targetPlaneEnergyDensity A u
  have hif := integrable_target_plane_energy hf A hA hfK hΛ
  have hiu := integrable_target_plane_energy hu A hA huK hΛ
  have hfρ : MapsTo f (Metric.closedBall (0 : ℂ) ρ) K :=
    hfK.mono_left (Metric.closedBall_subset_closedBall hρQ)
  have hAρ : AEStronglyMeasurable (fun z => A (f z))
      (volume.restrict (Metric.closedBall (0 : ℂ) ρ)) :=
    (hA.comp hf.continuous.continuousOn hfρ).aestronglyMeasurable measurableSet_closedBall
  have hboundρ : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) ρ), ‖A (f z)‖ ≤ Λ := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    exact hΛ _ (hfρ hz)
  have hcap : (∫ z in Metric.closedBall (0 : ℂ) ρ, ef z) ≤ Λ * B := by
    have h := norm_integral_quadratic_add_div_two_le (fun z => A (f z))
      (fun a b => (hAρ.apply_continuousLinearMap a).apply_continuousLinearMap b) hboundρ
      (memLp_fderiv_column_of_lipschitz hf (Q := ρ) 1)
      (memLp_fderiv_column_of_lipschitz hf (Q := ρ) Complex.I)
    exact (le_abs_self _).trans (h.trans (mul_le_mul_of_nonneg_left hfill hΛ0))
  have hext : (∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall 0 ρ, ef z) =
      ∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall 0 ρ, eu z := by
    apply setIntegral_congr_fun (measurableSet_closedBall.diff measurableSet_closedBall)
    intro z hz
    have hn : ρ < ‖z‖ := lt_of_not_ge (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2)
    have heq : f =ᶠ[𝓝 z] u := by
      have hnear := (continuous_norm.tendsto z) (isOpen_Ioi.mem_nhds hn)
      filter_upwards [hnear] with w hw
      exact hfix w hw.le
    dsimp only [ef, eu, targetPlaneEnergyDensity]
    rw [heq.eq_of_nhds, heq.fderiv_eq]
  have hsub : Metric.closedBall (0 : ℂ) Q \ Metric.closedBall 0 ρ ⊆
      Metric.closedBall (0 : ℂ) Q \ Metric.closedBall 0 r := by
    intro z hz
    exact ⟨hz.1, fun hr => hz.2 (Metric.closedBall_subset_closedBall hrρ hr)⟩
  have hnonneg : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) Q), 0 ≤ eu z := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    exact div_nonneg (add_nonneg (hpos _ (huK hz) _) (hpos _ (huK hz) _)) (by norm_num)
  have houter : (∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall 0 ρ, eu z) ≤
      ∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall 0 r, eu z :=
    setIntegral_mono_set (hiu.mono_set sdiff_subset)
      (ae_restrict_of_ae_restrict_of_subset sdiff_subset hnonneg) hsub.eventuallyLE
  have hsplit := setIntegral_sdiff measurableSet_closedBall hif
    (Metric.closedBall_subset_closedBall hρQ)
  rw [hext] at hsplit
  change (∫ z in Metric.closedBall (0 : ℂ) Q, ef z) ≤
    Λ * B + ∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall 0 r, eu z
  change (∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall 0 ρ, eu z) =
    (∫ z in Metric.closedBall (0 : ℂ) Q, ef z) -
      ∫ z in Metric.closedBall (0 : ℂ) ρ, ef z at hsplit
  linarith

section InnerProduct

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

theorem exists_radius_retracted_filling_target_energy_le
    {u : ℂ → G} {C : ℝ≥0} (hu : LipschitzWith C u) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    {K U : Set G} (huK : MapsTo u (Metric.closedBall (0 : ℂ) R) K)
    {η : ℝ} (hη : 0 < η) (htube : ∀ p ∈ K, Metric.ball p η ⊆ U)
    (hsmall : (2 * Real.pi * R / (R - r)) *
      (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖fderiv ℝ u z‖ ^ 2) < η ^ 2)
    (T : G → G) (hT : Differentiable ℝ T) {L : ℝ}
    (hL : ∀ x, ‖fderiv ℝ T x‖ ≤ L) (hTK : MapsTo T U K)
    (hfix : ∀ y ∈ K, T y = y)
    (A : G → G →L[ℝ] G →L[ℝ] ℝ) (hA : ContinuousOn A K)
    (hpos : ∀ y ∈ K, ∀ v, 0 ≤ A y v v)
    {Λ : ℝ} (hΛ : ∀ y ∈ K, ‖A y‖ ≤ Λ) (hΛ0 : 0 ≤ Λ) :
    ∃ ρ ∈ Icc r R, ∃ f : ℂ → G, (∃ C' : ℝ≥0, LipschitzWith C' f) ∧
      (∀ z, ρ ≤ ‖z‖ → f z = u z) ∧
      MapsTo f (Metric.closedBall (0 : ℂ) R) K ∧
      (∫ z in Metric.closedBall (0 : ℂ) R,
        (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
          A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2) ≤
        Λ * (5 * Real.pi ^ 2 * R / (R - r)) * L ^ 2 *
          (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖fderiv ℝ u z‖ ^ 2) +
        ∫ z in Metric.closedBall (0 : ℂ) R \ Metric.closedBall 0 r,
          (A (u z) (fderiv ℝ u z 1) (fderiv ℝ u z 1) +
            A (u z) (fderiv ℝ u z Complex.I) (fderiv ℝ u z Complex.I)) / 2 := by
  obtain ⟨ρ, hρ, f, ⟨Cf, hf⟩, htrace, _, htarget, henergy⟩ :=
    exists_radius_retracted_filling_energy_le_annulus hu hr hrR huK hη htube hsmall
      T hT hL hTK hfix
  refine ⟨ρ, hρ, f, ⟨Cf, hf⟩, htrace, htarget, ?_⟩
  have h := integral_target_energy_le_of_exterior_eq_of_filling_bound hf hu A hA hpos
    hΛ hΛ0 hρ.1 hρ.2 htarget huK htrace henergy
  simpa only [mul_assoc] using h

end InnerProduct

end DifferentialGeometry.Analysis

end
