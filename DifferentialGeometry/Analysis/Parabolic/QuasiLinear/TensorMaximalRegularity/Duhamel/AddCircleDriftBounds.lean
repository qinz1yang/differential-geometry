import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleLinearizedOperators
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.AffineMajorant

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

variable {ι : Type*} [Fintype ι]

theorem norm_parameterDriftOperatorHsPi_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :
    let D : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := parameterDerivativeHs g 1
    let m : TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := scalarHsMul g 1 (by norm_num)
    let d : TensorHs g 0 0 ((1 : ℕ) : ℝ) := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g))
    ‖parameterDriftOperatorHsPi (ι := ι) g a‖ ≤
      (‖m‖ * ‖D‖ ^ 2) * ‖a‖ + ‖m‖ * ‖d‖ * ‖D‖ := by
  intro D m d
  have hbase : ‖parameterDriftOperatorHsPi (ι := ι) g a‖ ≤
      ‖m‖ * ‖D a - d‖ * ‖D‖ := by
    apply ContinuousLinearMap.norm_piLpMap_le _ (by positivity)
    intro i
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (m.le_opNorm _) (norm_nonneg _))
  calc
    _ ≤ ‖m‖ * ‖D a - d‖ * ‖D‖ := hbase
    _ ≤ ‖m‖ * (‖D‖ * ‖a‖ + ‖d‖) * ‖D‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_sub_le (D a) d).trans (add_le_add (D.le_opNorm a) le_rfl)
    _ = _ := by ring

theorem norm_parameterDriftOperatorH0Pi_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let D : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := parameterDerivativeHs g 1
    let D₀ := Z.comp (parameterDerivativeHs g 0)
    let m := scalarH0ContinuousMul g
    let d : TensorHs g 0 0 ((1 : ℕ) : ℝ) := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g))
    ‖parameterDriftOperatorH0Pi (ι := ι) g a‖ ≤
      (‖m‖ * ‖C‖ * ‖D‖ * ‖D₀‖) * ‖a‖ + ‖m‖ * ‖C‖ * ‖d‖ * ‖D₀‖ := by
  intro C Z D D₀ m d
  have hbase : ‖parameterDriftOperatorH0Pi (ι := ι) g a‖ ≤
      ‖m‖ * (‖C‖ * ‖D a - d‖) * ‖D₀‖ := by
    apply ContinuousLinearMap.norm_piLpMap_le _ (by positivity)
    intro i
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact (m.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (C.le_opNorm _) (norm_nonneg _))
  calc
    _ ≤ ‖m‖ * (‖C‖ * ‖D a - d‖) * ‖D₀‖ := hbase
    _ ≤ ‖m‖ * (‖C‖ * (‖D‖ * ‖a‖ + ‖d‖)) * ‖D₀‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_sub_le (D a) d).trans (add_le_add (D.le_opNorm a) le_rfl)
    _ = _ := by ring

theorem norm_toLp_parameterDriftOperatorHsPi_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (a : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    let D : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := parameterDerivativeHs g 1
    let m : TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := scalarHsMul g 1 (by norm_num)
    let d : TensorHs g 0 0 ((1 : ℕ) : ℝ) := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g))
    let h := memLp_parameterDriftOperatorHsPi (ι := ι) g (Lp.memLp a)
    ‖h.toLp (fun t => parameterDriftOperatorHsPi (ι := ι) g (a t))‖ ≤
      (‖m‖ * ‖D‖ ^ 2) * ‖a‖ + Real.sqrt T * (‖m‖ * ‖d‖ * ‖D‖) := by
  intro D m d h
  apply timeL2_norm_le_of_ae_affine_bound _ a (by positivity) (by positivity)
  filter_upwards [h.coeFn_toLp] with t ht
  rw [ht]
  exact norm_parameterDriftOperatorHsPi_le g (a t)

theorem norm_toLp_parameterDriftOperatorH0Pi_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (a : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let D : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := parameterDerivativeHs g 1
    let D₀ := Z.comp (parameterDerivativeHs g 0)
    let m := scalarH0ContinuousMul g
    let d : TensorHs g 0 0 ((1 : ℕ) : ℝ) := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g))
    let h := memLp_parameterDriftOperatorH0Pi (ι := ι) g (Lp.memLp a)
    ‖h.toLp (fun t => parameterDriftOperatorH0Pi (ι := ι) g (a t))‖ ≤
      (‖m‖ * ‖C‖ * ‖D‖ * ‖D₀‖) * ‖a‖ +
        Real.sqrt T * (‖m‖ * ‖C‖ * ‖d‖ * ‖D₀‖) := by
  intro C Z D D₀ m d h
  apply timeL2_norm_le_of_ae_affine_bound _ a (by positivity) (by positivity)
  filter_upwards [h.coeFn_toLp] with t ht
  rw [ht]
  exact norm_parameterDriftOperatorH0Pi_le g (a t)

end AddCircle
