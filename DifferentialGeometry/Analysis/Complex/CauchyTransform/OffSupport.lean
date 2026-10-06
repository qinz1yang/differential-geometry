import DifferentialGeometry.Analysis.Complex.CauchyTransform.WeakEquation
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Convolution

namespace DifferentialGeometry.Analysis


variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The density is extended by zero solely for integration. No continuity
across the original disk boundary is asserted or used. -/
private def diskZeroExtension {a : ℂ} {R : ℝ} (f : C(closedBall a R, F)) (z : ℂ) : F := by
  classical
  exact if hz : z ∈ closedBall a R then f ⟨z, hz⟩ else 0

omit [NormedSpace ℂ F] [CompleteSpace F] in
private theorem diskZeroExtension_coe {a : ℂ} {R : ℝ}
    (f : C(closedBall a R, F)) (z : closedBall a R) :
    diskZeroExtension f z = f z := by
  simp only [diskZeroExtension, dite_eq_left z.property]

omit [NormedSpace ℂ F] [CompleteSpace F] in
private theorem diskZeroExtension_eq_zero {a : ℂ} {R : ℝ}
    (f : C(closedBall a R, F)) {z : ℂ} (hz : z ∉ closedBall a R) :
    diskZeroExtension f z = 0 := by
  simp only [diskZeroExtension, dite_eq_right hz]

omit [NormedSpace ℂ F] [CompleteSpace F] in
private theorem integrable_diskZeroExtension {a : ℂ} {R : ℝ}
    (f : C(closedBall a R, F)) : Integrable (diskZeroExtension f) := by
  have hc : ContinuousOn (diskZeroExtension f) (closedBall a R) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun z : closedBall a R => diskZeroExtension f z)
    simpa only [diskZeroExtension_coe] using f.continuous
  have hi : IntegrableOn (diskZeroExtension f) (closedBall a R) :=
    hc.integrableOn_compact (isCompact_closedBall a R)
  have he : (closedBall a R).indicator (diskZeroExtension f) = diskZeroExtension f := by
    funext z
    by_cases hz : z ∈ closedBall a R
    · exact indicator_of_mem hz _
    · simp only [indicator_of_notMem hz, diskZeroExtension_eq_zero f hz]
  rw [← he]
  exact hi.integrable_indicator measurableSet_closedBall

omit [CompleteSpace F] in
private theorem convolution_diskZeroExtension {a : ℂ} {R : ℝ}
    (f : C(closedBall a R, F)) (k : ℂ → ℂ) (z : ℂ) :
    (k ⋆[ContinuousLinearMap.lsmul ℝ ℂ, volume] diskZeroExtension f) z =
      ∫ w : closedBall a R, k (z - (w : ℂ)) • f w
        ∂(volume.comap ((↑) : closedBall a R → ℂ)) := by
  rw [convolution_eq_swap]
  change (∫ w : ℂ, k (z - w) • diskZeroExtension f w) = _
  have hout : ∀ w ∉ closedBall a R, k (z - w) • diskZeroExtension f w = 0 := by
    intro w hw
    rw [diskZeroExtension_eq_zero f hw, smul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout,
    ← integral_subtype_comap measurableSet_closedBall]
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by
    change k (z - (w : ℂ)) • diskZeroExtension f w = k (z - (w : ℂ)) • f w
    rw [diskZeroExtension_coe]

/-- A compact smooth modification of `1/z` agrees with the genuine kernel on
an annulus. The inner cutoff removes the singularity; no differentiability
of a zero-extended density is required by this construction. -/
private theorem exists_smooth_compact_inverse_kernel {d L : ℝ}
    (hd : 0 < d) (hL : 0 < L) :
    ∃ k : ℂ → ℂ, ContDiff ℝ ∞ k ∧ HasCompactSupport k ∧
      ∀ z : ℂ, d ≤ ‖z‖ → ‖z‖ ≤ L → k z = z⁻¹ := by
  let inner : ContDiffBump (0 : ℂ) := ⟨d / 2, d, by positivity, by linarith⟩
  let outer : ContDiffBump (0 : ℂ) := ⟨L, L + 1, hL, by linarith⟩
  let k : ℂ → ℂ := fun z => ((outer z : ℂ) * (1 - (inner z : ℂ))) * z⁻¹
  have houter : ContDiff ℝ ∞ (fun z : ℂ => (outer z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp outer.contDiff
  have hinner : ContDiff ℝ ∞ (fun z : ℂ => (inner z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp inner.contDiff
  have hk : ContDiff ℝ ∞ k := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z = 0
    · subst z
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℂ => (0 : ℂ)) 0).congr_of_eventuallyEq
      filter_upwards [inner.eventuallyEq_one] with z hz
      simp only [k, hz, Pi.one_apply, Complex.ofReal_one, sub_self, mul_zero, zero_mul]
    · exact (houter.contDiffAt.mul (contDiffAt_const.sub hinner.contDiffAt)).mul
        (contDiffAt_inv ℝ hz)
  have hkc : HasCompactSupport k := by
    apply HasCompactSupport.intro outer.hasCompactSupport.isCompact
    intro z hz
    have ho : outer z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp only [k, ho, Complex.ofReal_zero, zero_mul]
  refine ⟨k, hk, hkc, ?_⟩
  intro z hdz hzL
  have ho : outer z = 1 := outer.one_of_mem_closedBall (by
    simpa only [mem_closedBall, dist_zero_right, outer] using hzL)
  have hi : inner z = 0 := inner.zero_of_le_dist (by
    simpa only [dist_zero_right, inner] using hdz)
  simp only [k, ho, hi, Complex.ofReal_one, Complex.ofReal_zero, sub_zero, one_mul]

omit [CompleteSpace F] in
/-- The SAME ambient Cauchy integral is smooth at every point outside the
compact image of the actual density's support. This is the regularity of the
far term in an interior cutoff argument. Neither positive radius nor a
smooth density extension across the original circle is assumed. -/
theorem contDiffAt_ambientCauchyIntegral_off_support {a : ℂ} {R : ℝ}
    (f : C(closedBall a R, F)) {q : ℂ}
    (hq : q ∉ ((↑) : closedBall a R → ℂ) '' tsupport f) :
    ContDiffAt ℝ ∞ (ambientCauchyIntegral f) q := by
  let S : Set ℂ := ((↑) : closedBall a R → ℂ) '' tsupport f
  have hSc : IsCompact S := (isClosed_tsupport f).isCompact.image continuous_subtype_val
  obtain ⟨ε, hε, hgap⟩ := Metric.mem_nhds_iff.mp (hSc.isClosed.isOpen_compl.mem_nhds hq)
  let L : ℝ := dist q a + |R| + ε + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  obtain ⟨k, hk, hkc, hkeq⟩ := exists_smooth_compact_inverse_kernel
    (d := ε / 2) (L := L) (by positivity) hL
  have hsmooth : ContDiff ℝ ∞
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℂ, volume] diskZeroExtension f) :=
    hkc.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℂ) hk
      (integrable_diskZeroExtension f).locallyIntegrable
  have heq : ambientCauchyIntegral f =ᶠ[𝓝 q]
      (fun z => (Real.pi : ℂ)⁻¹ •
        (k ⋆[ContinuousLinearMap.lsmul ℝ ℂ, volume] diskZeroExtension f) z) := by
    filter_upwards [Metric.ball_mem_nhds q (show 0 < ε / 4 by positivity)] with z hz
    rw [ambientCauchyIntegral, convolution_diskZeroExtension]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun w => by
      by_cases hw : f w = 0
      · simp only [hw, smul_zero]
      have hwS : (w : ℂ) ∈ S :=
        ⟨w, subset_tsupport f (Function.mem_support.mpr hw), rfl⟩
      have hlow : ε / 2 ≤ ‖z - (w : ℂ)‖ := by
        by_contra hh
        have hdzw : dist z (w : ℂ) < ε / 2 := by
          simpa only [dist_eq_norm] using lt_of_not_ge hh
        have hdzq : dist z q < ε / 4 := hz
        have hwd : dist (w : ℂ) q < ε := by
          have ht := dist_triangle (w : ℂ) z q
          rw [dist_comm (w : ℂ) z] at ht
          linarith
        exact (hgap hwd) hwS
      have hupp : ‖z - (w : ℂ)‖ ≤ L := by
        have hdzq : dist z q < ε / 4 := hz
        have hdwa : dist a (w : ℂ) ≤ R := by
          simpa only [mem_closedBall, dist_comm] using w.property
        have ht₁ := dist_triangle z q (w : ℂ)
        have ht₂ := dist_triangle q a (w : ℂ)
        rw [← dist_eq_norm]
        dsimp only [L]
        linarith [le_abs_self R]
      change (z - (w : ℂ))⁻¹ • f w = k (z - (w : ℂ)) • f w
      rw [hkeq (z - (w : ℂ)) hlow hupp]
  exact (contDiffAt_const.smul hsmooth.contDiffAt).congr_of_eventuallyEq heq

end DifferentialGeometry.Analysis
