import DifferentialGeometry.Analysis.Sobolev.Euclidean.LipschitzWitness
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuant
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.FDeriv.Equiv

section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_memW01p_smooth_mul_bounds_of_lipschitz
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩbdd : Bornology.IsBounded Ω)
    {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : E → ℝ} {K : ℝ≥0} {A B : ℝ},
      LipschitzWith K f → (∫ x in Ω, f x ^ 2) ≤ A →
      (∫ x in Ω, ‖fderiv ℝ f x‖ ^ 2) ≤ B →
        DeGiorgi.MemW01p 2 (fun x => η x * f x) Ω ∧
        eLpNorm (fun x => η x * f x) 2 (volume.restrict Ω) ≤
          ENNReal.ofReal (C * (Real.sqrt A + Real.sqrt B)) ∧
        ∀ hw : DeGiorgi.MemW1pWitness 2 (fun x => η x * f x) Ω, ∀ i : Fin d,
          eLpNorm (fun x => hw.weakGrad x i) 2 (volume.restrict Ω) ≤
            ENNReal.ofReal (C * (Real.sqrt A + Real.sqrt B)) := by
  obtain ⟨C₀, hC₀⟩ := hη.continuous.bounded_above_of_compact_support hηc
  obtain ⟨C₁, hC₁⟩ := (hη.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hηc.fderiv (𝕜 := ℝ))
  let C := max 0 (max C₀ C₁)
  have hC : 0 ≤ C := le_max_left _ _
  have hηbound : ∀ x, |η x| ≤ C := fun x => by
    simpa only [Real.norm_eq_abs] using
      (hC₀ x).trans ((le_max_left C₀ C₁).trans (le_max_right 0 _))
  have hdηbound : ∀ x, ‖fderiv ℝ η x‖ ≤ C := fun x =>
    (hC₁ x).trans ((le_max_right C₀ C₁).trans (le_max_right 0 _))
  refine ⟨C, hC, ?_⟩
  intro f K A B hf hA hB
  let _ : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩbdd.measure_lt_top.ne
  obtain ⟨F, hF⟩ := hΩbdd.isCompact_closure.exists_bound_of_continuousOn
    hf.continuous.continuousOn
  have hfm : MemLp f 2 (volume.restrict Ω) := by
    refine MemLp.of_bound hf.continuous.aestronglyMeasurable F ?_
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    exact hF x (subset_closure hx)
  have hdfm : MemLp (fderiv ℝ f) 2 (volume.restrict Ω) :=
    MemLp.of_bound
      ((measurable_fderiv ℝ f).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
      K (Eventually.of_forall fun x => norm_fderiv_le_of_lipschitz ℝ hf)
  obtain ⟨hu, hrep, _⟩ := exists_memW1pWitness_fderiv_of_lipschitz hf hfm hdfm
  let hv := hu.mulSmoothBoundedP (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hΩ hη hC hC hηbound hdηbound
  have hvcompact : HasCompactSupport (fun x => η x * f x) := hηc.mul_right
  have hvsupport : tsupport (fun x => η x * f x) ⊆ Ω :=
    tsupport_mul_subset_left.trans hηΩ
  have hvzero : DeGiorgi.MemW01p 2 (fun x => η x * f x) Ω := by
    by_cases hd : d = 0
    · subst d
      have hconst : (fun x => η x * f x) = fun _ => η 0 * f 0 := by
        funext x
        rw [Subsingleton.elim x 0]
      refine ⟨hv.memW1p, hv, fun _ => (fun x => η x * f x), ?_,
        fun _ => hvcompact, fun _ => hvsupport, ?_, ?_⟩
      · intro n
        rw [hconst]
        exact contDiff_const
      · simp
      · exact fun i => Fin.elim0 i
    · let : NeZero d := ⟨hd⟩
      simpa using DeGiorgi.memW01p_of_memW1p_of_tsupport_subset
        hΩ (p := 2) (by norm_num) (by simpa using hv.memW1p) hvcompact hvsupport
  have hfun : eLpNorm f 2 (volume.restrict Ω) ≤ ENNReal.ofReal (Real.sqrt A) := by
    apply DifferentialGeometry.Analysis.Integration.eLpNorm_two_le_of_integral_norm_sq_le hfm
    simpa only [Real.norm_eq_abs, sq_abs] using hA
  have hderiv : eLpNorm (fderiv ℝ f) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal (Real.sqrt B) :=
    DifferentialGeometry.Analysis.Integration.eLpNorm_two_le_of_integral_norm_sq_le hdfm hB
  have hpartial (i : Fin d) : eLpNorm (fun x => hu.weakGrad x i) 2
      (volume.restrict Ω) ≤ ENNReal.ofReal (Real.sqrt B) := by
    refine (eLpNorm_mono (hu.weakGrad_component_memLp i).aestronglyMeasurable
      fun x => ?_).trans hderiv
    rw [hrep x i]
    simpa using (fderiv ℝ f x).le_opNorm (EuclideanSpace.single i 1)
  have hfactor : ENNReal.ofReal (C * (Real.sqrt A + Real.sqrt B)) =
      ENNReal.ofReal C *
        (ENNReal.ofReal (Real.sqrt A) + ENNReal.ofReal (Real.sqrt B)) := by
    rw [ENNReal.ofReal_mul hC,
      ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  refine ⟨hvzero, ?_, ?_⟩
  · rw [hfactor]
    refine (eLpNorm_eta_mul_le hΩ
      (fun x _ => by simpa only [Real.norm_eq_abs] using hηbound x) f
      (hη.continuous.aestronglyMeasurable.mul hfm.aestronglyMeasurable)).trans ?_
    exact mul_le_mul_right (hfun.trans (le_self_add)) _
  · intro hw i
    let : NeZero d := ⟨fun hd => by simpa [hd] using i.isLt⟩
    have hae : (fun x => hw.weakGrad x i) =ᵐ[volume.restrict Ω]
        (fun x => hv.weakGrad x i) := by
      filter_upwards [DeGiorgi.MemW1pWitness.ae_eq hΩ hw hv] with x hx
      rw [hx]
    rw [eLpNorm_congr_ae hae, hfactor]
    have heq : (fun x => hv.weakGrad x i) =
        (fun x => η x * hu.weakGrad x i) +
          (fun x => fderiv ℝ η x (EuclideanSpace.single i 1) * f x) := by
      funext x
      rfl
    rw [heq]
    have hfirst : AEStronglyMeasurable (fun x => η x * hu.weakGrad x i)
        (volume.restrict Ω) :=
      hη.continuous.aestronglyMeasurable.mul (hu.weakGrad_component_memLp i).aestronglyMeasurable
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    have hleft := (eLpNorm_eta_mul_le hΩ
      (fun x _ => by simpa only [Real.norm_eq_abs] using hηbound x)
      (fun x => hu.weakGrad x i) hfirst).trans (mul_le_mul_right (hpartial i) _)
    have hright := (eLpNorm_partial_eta_mul_le hΩ (fun x _ => hdηbound x) i f).trans
      (mul_le_mul_right hfun _)
    calc
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt B) +
          ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt A) := add_le_add hleft hright
      _ = _ := by rw [← mul_add, add_comm (ENNReal.ofReal (Real.sqrt B))]

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

section

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

theorem exists_memW01p_complex_cutoff_bounds_of_lipschitz
    {η : ℂ → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηball : tsupport η ⊆ ball (0 : ℂ) 1) :
    let e := Complex.orthonormalBasisOneI.repr.symm
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : ℂ → ℝ} {K : ℝ≥0} {A B : ℝ},
      LipschitzWith K f → (∫ z in ball (0 : ℂ) 1, f z ^ 2) ≤ A →
      (∫ z in ball (0 : ℂ) 1, ‖fderiv ℝ f z‖ ^ 2) ≤ B →
        DeGiorgi.MemW01p 2 (fun x => η (e x) * f (e x)) (ball 0 1) ∧
        eLpNorm (fun x => η (e x) * f (e x)) 2 (volume.restrict (ball 0 1)) ≤
          ENNReal.ofReal (C * (Real.sqrt A + Real.sqrt B)) ∧
        ∀ hw : DeGiorgi.MemW1pWitness 2 (fun x => η (e x) * f (e x)) (ball 0 1),
          ∀ i : Fin 2, eLpNorm (fun x => hw.weakGrad x i) 2
            (volume.restrict (ball 0 1)) ≤
              ENNReal.ofReal (C * (Real.sqrt A + Real.sqrt B)) := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  have hball : e ⁻¹' ball (0 : ℂ) 1 = ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    ext x
    simp only [mem_preimage, mem_ball_zero_iff, e.norm_map]
  have hint (q : ℂ → ℝ) :
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, q (e x)) =
        ∫ z in ball (0 : ℂ) 1, q z := by
    simpa only [hball] using e.measurePreserving.setIntegral_preimage_emb
      e.toHomeomorph.measurableEmbedding q (ball (0 : ℂ) 1)
  have hηe : ContDiff ℝ ∞ (η ∘ e) := hη.comp e.toContinuousLinearEquiv.contDiff
  have hηec : HasCompactSupport (η ∘ e) := hηc.comp_homeomorph e.toHomeomorph
  have hηeb : tsupport (η ∘ e) ⊆ ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    rw [← hball]
    exact (tsupport_comp_subset_preimage η e.continuous).trans (preimage_mono hηball)
  obtain ⟨C, hC, hcut⟩ := Euclidean.exists_memW01p_smooth_mul_bounds_of_lipschitz
    isOpen_ball isBounded_ball hηe hηec hηeb
  refine ⟨C, hC, ?_⟩
  intro f K A B hf hA hB
  have hfe : LipschitzWith K (f ∘ e) := by
    simpa only [mul_one] using hf.comp e.lipschitzWith
  have hAe : (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, (f ∘ e) x ^ 2) ≤ A := by
    change (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, f (e x) ^ 2) ≤ A
    rw [hint (fun z => f z ^ 2)]
    exact hA
  have hnorm (x : EuclideanSpace ℝ (Fin 2)) :
      ‖fderiv ℝ (f ∘ e) x‖ = ‖fderiv ℝ f (e x)‖ := by
    change ‖fderiv ℝ (f ∘ (e.toContinuousLinearEquiv : _ → _)) x‖ = _
    rw [e.toContinuousLinearEquiv.comp_right_fderiv]
    exact (fderiv ℝ f (e x)).opNorm_comp_linearIsometryEquiv e
  have hBe : (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ‖fderiv ℝ (f ∘ e) x‖ ^ 2) ≤ B := by
    simp_rw [hnorm]
    rw [hint (fun z => ‖fderiv ℝ f z‖ ^ 2)]
    exact hB
  exact hcut hfe hAe hBe

end DifferentialGeometry.Analysis.Sobolev

end

end
