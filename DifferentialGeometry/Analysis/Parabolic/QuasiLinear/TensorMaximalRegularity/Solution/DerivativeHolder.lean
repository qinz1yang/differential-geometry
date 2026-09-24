import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleAgmon
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Regularity.Holder
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.ContinuousRepresentative
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open scoped NNReal ENNReal

private theorem holderOnWith_of_norm_sub_sq_le {X : Type*} [NormedAddCommGroup X]
    {f : ℝ → X} {K : Set ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ t ∈ K, ∀ z ∈ K, ‖f t - f z‖ ^ 2 ≤ B * Real.sqrt |t - z|) :
    HolderOnWith (Real.toNNReal (Real.sqrt B)) (1 / 4) f K := by
  intro t ht z hz
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ (by positivity),
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  change (nndist _ _ : ℝ) ≤ (_ : ℝ≥0)
  simp only [coe_nndist, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat, dist_eq_norm, Real.norm_eq_abs,
    Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  have hsqrt := (Real.le_sqrt (norm_nonneg _) (mul_nonneg hB (Real.sqrt_nonneg _))).mpr
    (h t ht z hz)
  refine hsqrt.trans_eq ?_
  rw [Real.sqrt_mul hB]
  simp_rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (abs_nonneg _)]
  norm_num

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private theorem exists_holderOnWith_of_agmon
    {X Y Z V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {T : ℝ} (j : X →L[ℝ] Z) (e : Y →L[ℝ] Z) (r : X →L[ℝ] V)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ‖r x‖ ^ 2 ≤ C * ‖j x‖ * ‖x‖)
    (u : timeH1 Y T) (v : ℝ → X) (hv : ContinuousOn v (Set.Icc 0 T))
    (heq : ∀ t ∈ Set.Icc 0 T, j (v t) = e (u.toFun t)) :
    ∃ C : ℝ≥0, HolderOnWith C (1 / 4) (fun t => r (v t)) (Set.Icc 0 T) := by
  obtain ⟨C, hC, hbound⟩ := h
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
  let B := C * (‖e‖ * ‖u.deriv‖) * (2 * max M 0)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨Real.toNNReal (Real.sqrt B), holderOnWith_of_norm_sub_sq_le hB ?_⟩
  intro t ht z hz
  rw [← map_sub]
  have hlow : ‖j (v t - v z)‖ ≤ (‖e‖ * ‖u.deriv‖) * Real.sqrt |t - z| := by
    rw [map_sub, heq t ht, heq z hz, ← map_sub]
    calc
      _ ≤ ‖e‖ * ‖u.toFun t - u.toFun z‖ := e.le_opNorm _
      _ ≤ ‖e‖ * (Real.sqrt |t - z| * ‖u.deriv‖) :=
        mul_le_mul_of_nonneg_left (u.toFun_sub_le hz ht) (norm_nonneg _)
      _ = _ := by ring
  have hhigh : ‖v t - v z‖ ≤ 2 * max M 0 := by
    have ht' := (hM t ht).trans (le_max_left M 0)
    have hz' := (hM z hz).trans (le_max_left M 0)
    exact (norm_sub_le _ _).trans (by linarith)
  calc
    _ ≤ C * ‖j (v t - v z)‖ * ‖v t - v z‖ := hbound _
    _ ≤ C * ((‖e‖ * ‖u.deriv‖) * Real.sqrt |t - z|) * (2 * max M 0) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlow hC) hhigh (norm_nonneg _)
        (by positivity)
    _ = _ := by dsimp only [B]; ring

open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private def derivativeH2H1
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    TensorHs g 0 0 2 →L[ℝ] TensorHs g 0 0 1 :=
  (tensorHsInclusion (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)).comp
    ((parameterDerivativeHs g 1).comp
      (tensorHsInclusion (show ((1 : ℕ) : ℝ) + 1 ≤ 2 by norm_num)))

private def derivativeH1H0
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    TensorHs g 0 0 1 →L[ℝ] TensorHs g 0 0 0 :=
  (tensorHsInclusion (show (0 : ℝ) ≤ ((0 : ℕ) : ℝ) by norm_num)).comp
    ((parameterDerivativeHs g 0).comp
      (tensorHsInclusion (show ((0 : ℕ) : ℝ) + 1 ≤ 1 by norm_num)))

private theorem derivativeH2H1_inclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : TensorHs g 0 0 2) :
    tensorHsInclusion (show (0 : ℝ) ≤ 1 by norm_num) (derivativeH2H1 g u) =
      derivativeH1H0 g (tensorHsInclusion (show (1 : ℝ) ≤ 2 by norm_num) u) := by
  dsimp only [derivativeH2H1, derivativeH1H0, ContinuousLinearMap.comp_apply]
  rw [← tensorHsInclusion_trans_apply, ← tensorHsInclusion_trans_apply]
  have h := parameterDerivativeHs_tensorHsInclusion g (by norm_num : 0 ≤ 1)
    (tensorHsInclusion (show ((1 : ℕ) : ℝ) + 1 ≤ 2 by norm_num) u)
  rw [← tensorHsInclusion_trans_apply] at h
  rw [h, ← tensorHsInclusion_trans_apply]

variable {ι : Type*} {T : ℝ}

private def derivativeH2H1Pi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 2) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 1) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι => derivativeH2H1 g)

private theorem derivativeH2H1Pi_inclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 2)) :
    ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (show (0 : ℝ) ≤ 1 by norm_num)) (derivativeH2H1Pi g u) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => derivativeH1H0 g))
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (show (1 : ℝ) ≤ 2 by norm_num)) u) := by
  apply PiLp.ext
  intro i
  exact derivativeH2H1_inclusion g (u i)

private theorem exists_holderOnWith_derivativeH2H1Pi [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) T)
    (w : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 2))
    (hw : ContinuousOn w (Set.Icc 0 T))
    (hproducer : ∀ t ∈ Set.Icc 0 T,
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (show (1 : ℝ) ≤ 2 by norm_num)) (w t) = u.toFun t) :
    ∃ C : ℝ≥0, HolderOnWith C (1 / 4)
      (fun t => scalarH1PiToContinuous g (derivativeH2H1Pi g (w t)))
      (Set.Icc 0 T) := by
  let j := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0) (show (0 : ℝ) ≤ 1 by norm_num))
  let e := ContinuousLinearMap.piLpMap 2 (fun _ : ι => derivativeH1H0 g)
  let r := scalarH1PiToContinuous (ι := ι) g
  obtain ⟨C, hC, hbound⟩ := exists_norm_scalarH1PiToContinuous_sq_le (ι := ι) g
  refine exists_holderOnWith_of_agmon j e r ?_ u (fun t => derivativeH2H1Pi g (w t)) ?_ ?_
  · refine ⟨C, hC, ?_⟩
    intro x
    exact hbound x
  · exact (derivativeH2H1Pi g).continuous.comp_continuousOn hw
  · intro t ht
    change j (derivativeH2H1Pi g (w t)) = e (u.toFun t)
    dsimp only [j, e]
    rw [derivativeH2H1Pi_inclusion g (w t), hproducer t ht]

theorem exists_holderOnWith_parameterDerivativeHsPi [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) T)
    (w : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 2))
    (hw : ContinuousOn w (Set.Icc 0 T))
    (hproducer : ∀ t ∈ Set.Icc 0 T,
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (show (1 : ℝ) ≤ 2 by norm_num)) (w t) = u.toFun t) :
    ∃ C : ℝ≥0, HolderOnWith C (1 / 4)
      (fun t => scalarH1PiToContinuous g
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num))
          (parameterDerivativeHsPi g 1
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorHsInclusion (show ((1 : ℕ) : ℝ) + 1 ≤ 2 by norm_num)) (w t)))))
      (Set.Icc 0 T) := by
  exact exists_holderOnWith_derivativeH2H1Pi g u w hw hproducer

end AddCircle

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev
open DifferentialGeometry.Analysis.Spectral

variable {ι : Type*} [Fintype ι]

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem maximalRegularityDuhamelVectorMap_exists_holderOnWith_parameterDerivative
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℝ) + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) T) :
    ∃ w : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 2),
      ContinuousOn w (Set.Icc 0 T) ∧
      (∀ t ∈ Set.Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (1 : ℝ) ≤ 2 by norm_num)) (w t) =
        (maximalRegularityDuhamelVectorMap hT u₀ F).toFun t) ∧
      (w =ᵐ[timeMeasure T] fun t => ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (2 : ℝ) ≤ (1 : ℝ) + 2 by norm_num))
          (maximalRegularityDuhamelVectorField hT u₀ F t)) ∧
      ∃ C : ℝ≥0, HolderOnWith C (1 / 4)
        (fun t => scalarH1PiToContinuous g
          (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num))
            (AddCircle.parameterDerivativeHsPi g 1
              (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
                tensorHsInclusion (show ((1 : ℕ) : ℝ) + 1 ≤ 2 by norm_num)) (w t)))))
        (Set.Icc 0 T) := by
  obtain ⟨w, hw, hlo, hhi⟩ :=
    maximalRegularityDuhamelVectorMap_exists_continuousOn_representative hT
      (tensorResolventL2_isCompactOperator
        (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0) u₀ F
  let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (2 : ℝ) ≤ (1 : ℝ) + 1 by norm_num))
  have hw' : ContinuousOn (fun t => L (w t)) (Set.Icc 0 T) :=
    L.continuous.comp_continuousOn hw
  have hlo' : ∀ t ∈ Set.Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show (1 : ℝ) ≤ 2 by norm_num)) (L (w t)) =
      (maximalRegularityDuhamelVectorMap hT u₀ F).toFun t := by
    intro t ht
    rw [← hlo t ht]
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply (by norm_num) (by norm_num) (w t i)).symm
  refine ⟨fun t => L (w t), hw', hlo', ?_, ?_⟩
  · filter_upwards [hhi] with t ht
    rw [ht]
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply (by norm_num) (by norm_num)
      (maximalRegularityDuhamelVectorField hT u₀ F t i)).symm
  · exact AddCircle.exists_holderOnWith_parameterDerivativeHsPi g
      (maximalRegularityDuhamelVectorMap hT u₀ F) (fun t => L (w t)) hw' hlo'

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
