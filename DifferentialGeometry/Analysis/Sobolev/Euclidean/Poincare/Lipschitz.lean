import DifferentialGeometry.Analysis.Sobolev.Euclidean.LipschitzWitness
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Poincare
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.FDeriv.Equiv

section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_integral_sq_le_mul_integral_norm_fderiv_sq_of_lipschitz
    {Ω : Set E} (hd : 2 ≤ d) (hΩ : IsOpen Ω) (hΩbdd : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : E → ℝ} {K : ℝ≥0},
      LipschitzWith K f → HasCompactSupport f → tsupport f ⊆ Ω →
        (∫ x in Ω, f x ^ 2) ≤ C * ∫ x in Ω, ‖fderiv ℝ f x‖ ^ 2 := by
  let _ : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hP⟩ := exists_poincare_constant hd hΩ hΩbdd
  refine ⟨C ^ 2, sq_nonneg _, ?_⟩
  intro f K hf hcompact hsupport
  let _ : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩbdd.measure_lt_top.ne
  have hfm : MemLp f 2 (volume.restrict Ω) :=
    (hf.continuous.memLp_of_hasCompactSupport hcompact).restrict Ω
  have hdfm : MemLp (fderiv ℝ f) 2 (volume.restrict Ω) :=
    MemLp.of_bound
      ((measurable_fderiv ℝ f).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
      K (Filter.Eventually.of_forall fun x => norm_fderiv_le_of_lipschitz ℝ hf)
  obtain ⟨hw, _, hnorm⟩ := exists_memW1pWitness_fderiv_of_lipschitz hf hfm hdfm
  have hw0 : DeGiorgi.MemW01p 2 f Ω := by
    simpa using DeGiorgi.memW01p_of_memW1p_of_tsupport_subset
      hΩ (p := 2) (by norm_num) (by simpa using hw.memW1p) hcompact hsupport
  have hp := hP hw0 hw
  have hsq : ‖hw.memLp.toLp f‖ ^ 2 = ∫ x in Ω, f x ^ 2 := by
    rw [Lp.norm_toLp]
    exact (DifferentialGeometry.Analysis.Integration.integral_sq_eq_l2 hfm).symm
  have hgrad : ‖DeGiorgi.gradLpOfWitness hw‖ ^ 2 =
      ∫ x in Ω, ‖fderiv ℝ f x‖ ^ 2 := by
    rw [DeGiorgi.gradLpOfWitness, Lp.norm_toLp, hnorm]
    rw [← eLpNorm_norm (fderiv ℝ f) hdfm.aestronglyMeasurable]
    exact (DifferentialGeometry.Analysis.Integration.integral_sq_eq_l2 hdfm.norm).symm
  have hp2 := (sq_le_sq₀ (norm_nonneg (hw.memLp.toLp f))
    (mul_nonneg hC (norm_nonneg (DeGiorgi.gradLpOfWitness hw)))).mpr hp
  rw [mul_pow, hsq, hgrad] at hp2
  exact hp2

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev

theorem exists_integral_sq_le_mul_integral_norm_fderiv_sq_complex_ball_of_lipschitz :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : ℂ → ℝ} {K : ℝ≥0},
      LipschitzWith K f → HasCompactSupport f → tsupport f ⊆ ball 0 1 →
        (∫ z in ball (0 : ℂ) 1, f z ^ 2) ≤
          C * ∫ z in ball (0 : ℂ) 1, ‖fderiv ℝ f z‖ ^ 2 := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  have hball : e ⁻¹' ball (0 : ℂ) 1 = ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    ext x
    simp only [mem_preimage, mem_ball_zero_iff, e.norm_map]
  have hint (q : ℂ → ℝ) :
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, q (e x)) =
        ∫ z in ball (0 : ℂ) 1, q z := by
    simpa only [hball] using e.measurePreserving.setIntegral_preimage_emb
      e.toHomeomorph.measurableEmbedding q (ball (0 : ℂ) 1)
  obtain ⟨C, hC, hP⟩ := Euclidean.exists_integral_sq_le_mul_integral_norm_fderiv_sq_of_lipschitz
    (d := 2) (Ω := ball 0 1) (by norm_num) isOpen_ball isBounded_ball
  refine ⟨C, hC, ?_⟩
  intro f K hf hcompact hsupport
  have hfe : LipschitzWith K (f ∘ e) := by
    simpa only [mul_one] using hf.comp e.lipschitzWith
  have hcompacte : HasCompactSupport (f ∘ e) := hcompact.comp_homeomorph e.toHomeomorph
  have hsupporte : tsupport (f ∘ e) ⊆ ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    rw [← hball]
    exact (tsupport_comp_subset_preimage f e.continuous).trans (preimage_mono hsupport)
  have hnorm (x : EuclideanSpace ℝ (Fin 2)) :
      ‖fderiv ℝ (f ∘ e) x‖ = ‖fderiv ℝ f (e x)‖ := by
    change ‖fderiv ℝ (f ∘ (e.toContinuousLinearEquiv : _ → _)) x‖ = _
    rw [e.toContinuousLinearEquiv.comp_right_fderiv]
    exact (fderiv ℝ f (e x)).opNorm_comp_linearIsometryEquiv e
  have hp := hP hfe hcompacte hsupporte
  calc
    (∫ z in ball (0 : ℂ) 1, f z ^ 2) =
        ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, (f ∘ e) x ^ 2 := by
      simpa only [Function.comp_apply] using (hint (fun z => f z ^ 2)).symm
    _ ≤ C * ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, ‖fderiv ℝ (f ∘ e) x‖ ^ 2 := hp
    _ = C * ∫ z in ball (0 : ℂ) 1, ‖fderiv ℝ f z‖ ^ 2 := by
      rw [show (fun x => ‖fderiv ℝ (f ∘ e) x‖ ^ 2) =
        (fun x => ‖fderiv ℝ f (e x)‖ ^ 2) by
          funext x; rw [hnorm]]
      congr 1
      exact hint (fun z => ‖fderiv ℝ f z‖ ^ 2)

end DifferentialGeometry.Analysis.Sobolev

end

end
