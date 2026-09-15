import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.DerivativeHolder
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleClassicalDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleHolder
import DifferentialGeometry.Analysis.Schauder.Holder.CompactRegularity
import DifferentialGeometry.Analysis.Schauder.Holder.ParabolicSlices
import Mathlib.Topology.MetricSpace.HolderNorm

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Schauder

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

variable {ι : Type*} [Fintype ι]

private def spatialDerivative
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 2) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 1) :=
  (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num))).comp
      ((AddCircle.parameterDerivativeHsPi g 1).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (show ((1 : ℕ) : ℝ) + 1 ≤ 2 by norm_num))))

private theorem hasDerivAt_realization
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) T)
    (w : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 2))
    (hproducer : ∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (show (1 : ℝ) ≤ 2 by norm_num)) (w t) = u.toFun t)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    HasDerivAt (fun y : ℝ => scalarH1PiToContinuous g (u.toFun t)
      (y : AddCircle (1 : ℝ)))
      (scalarH1PiToContinuous g (spatialDerivative g (w t)) (x : AddCircle (1 : ℝ))) x := by
  let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show ((1 : ℕ) : ℝ) + 1 ≤ 2 by norm_num))
  have h := AddCircle.hasDerivAt_scalarH1PiToContinuous g (L (w t)) x
  have hlo : ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 by norm_num)) (L (w t)) = u.toFun t := by
    rw [← hproducer t ht]
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply (by norm_num) (by norm_num) (w t i)).symm
  rw [hlo] at h
  exact h

private theorem exists_holderOnWith_time_coordinate (T : ℝ) :
    ∃ C : ℝ≥0, HolderOnWith C (1 / 2) (fun p : ParabolicPoint ℝ => p.time)
      (parabolicCylinder (Icc 0 T) (Icc 0 1)) := by
  obtain ⟨C, hC⟩ := exists_holderWith_restrict_parabolicCylinder_Icc_of_contDiffOn
    (0 : ℝ) T isCompact_Icc (convex_Icc 0 1)
    (contDiff_fst.contDiffOn : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => p.1)
      (Icc 0 T ×ˢ Icc 0 1)) (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)
  exact ⟨C, HolderWith.restrict_iff.mp hC⟩

private theorem exists_holderOnWith_time_realization
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) T) :
    ∃ C : ℝ≥0, HolderOnWith C (1 / 4)
      (fun t => scalarH1PiToContinuous g (u.toFun t)) (Icc 0 T) := by
  have h := (scalarH1PiToContinuous (ι := ι) g).lipschitz.holderWith.comp_holderOnWith
    u.holderOnWith_toFun
  have hhalf : ∃ C : ℝ≥0, HolderOnWith C (1 / 2)
      (fun t => scalarH1PiToContinuous g (u.toFun t)) (Icc 0 T) := by
    refine ⟨‖scalarH1PiToContinuous (ι := ι) g‖₊ * ‖u.deriv‖₊, ?_⟩
    simpa only [Function.comp_def, one_mul, NNReal.coe_one, NNReal.rpow_one] using h
  exact HolderOnWith.exists_holderOnWith_of_le hhalf (by norm_num [← NNReal.coe_le_coe] : (1 / 4 : ℝ≥0) ≤ 1 / 2) isCompact_Icc.isBounded

private theorem holderOnWith_evaluation {X F : Type*} [TopologicalSpace X] [CompactSpace X]
    [PseudoMetricSpace F] {J : Set ℝ} {A α : ℝ≥0} {f : ℝ → C(X, F)}
    (h : HolderOnWith A α f J) (x : X) :
    HolderOnWith A α (fun t => f t x) J := by
  have hx : LipschitzWith 1 (fun u : C(X, F) => u x) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simpa only [NNReal.coe_one, one_mul] using ContinuousMap.dist_apply_le_dist x
  simpa only [Function.comp_apply, one_mul, NNReal.coe_one, NNReal.rpow_one] using!
    hx.holderWith.comp_holderOnWith h

private theorem exists_uniform_spatial_holder
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    {f : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 1)}
    (hf : ContinuousOn f (Icc 0 T)) :
    ∃ B : ℝ≥0, ∀ t ∈ Icc 0 T, HolderOnWith B (1 / 2)
      (fun x : ℝ => scalarH1PiToContinuous g (f t) (x : AddCircle (1 : ℝ)))
      (Icc 0 1) := by
  obtain ⟨C, hC, hbound⟩ := AddCircle.exists_scalarH1PiToContinuous_coe_sub_le (ι := ι) g
  obtain ⟨R, hR⟩ := exists_norm_bound_of_continuousOn_isCompact isCompact_Icc hf
  refine ⟨⟨C * R, mul_nonneg hC R.coe_nonneg⟩, ?_⟩
  intro t ht x hx y hy
  have hreal : dist (scalarH1PiToContinuous g (f t) (x : AddCircle (1 : ℝ)))
      (scalarH1PiToContinuous g (f t) (y : AddCircle (1 : ℝ))) ≤
      (C * R) * dist x y ^ ((1 / 2 : ℝ≥0) : ℝ) := by
    simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat, ← Real.sqrt_eq_rpow]
    exact (hbound (f t) x y hx hy).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hR t ht) hC) (Real.sqrt_nonneg _))
  rw [edist_dist, edist_dist]
  calc
    ENNReal.ofReal _ ≤ ENNReal.ofReal ((C * R) * dist x y ^ ((1 / 2 : ℝ≥0) : ℝ)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg hC R.coe_nonneg),
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity)]
      congr 1
      exact ENNReal.ofReal_eq_coe_nnreal (mul_nonneg hC R.coe_nonneg)

private theorem exists_joint_holder
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    {f : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 1)}
    (hf : ContinuousOn f (Icc 0 T))
    (ht : ∃ A : ℝ≥0, HolderOnWith A (1 / 4)
      (fun t => scalarH1PiToContinuous g (f t)) (Icc 0 T)) :
    ∃ C : ℝ≥0, HolderOnWith C (1 / 2)
      (fun p : ParabolicPoint ℝ => scalarH1PiToContinuous g (f p.time)
        (p.space : AddCircle (1 : ℝ))) (parabolicCylinder (Icc 0 T) (Icc 0 1)) := by
  obtain ⟨A, hA⟩ := ht
  obtain ⟨B, hB⟩ := exists_uniform_spatial_holder g hf
  refine ⟨A + B, holderOnWith_parabolicCylinder_of_slices ?_ hB⟩
  intro x _
  have heq : (1 / 2 : ℝ≥0) / 2 = 1 / 4 := by norm_num [← NNReal.coe_inj]
  rw [heq]
  exact holderOnWith_evaluation hA (x : AddCircle (1 : ℝ))

theorem exists_holderOnWith_firstJet_of_timeH1
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) T)
    (w : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 2))
    (hw : ContinuousOn w (Icc 0 T))
    (hproducer : ∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (show (1 : ℝ) ≤ 2 by norm_num)) (w t) = u.toFun t) :
    ∃ C : ℝ≥0, HolderOnWith C (1 / 2)
      (fun p : ParabolicPoint ℝ => (p.time,
        scalarH1PiToContinuous g (u.toFun p.time) (p.space : AddCircle (1 : ℝ)),
        deriv (fun x : ℝ => scalarH1PiToContinuous g (u.toFun p.time)
          (x : AddCircle (1 : ℝ))) p.space))
      (parabolicCylinder (Icc 0 T) (Icc 0 1)) := by
  obtain ⟨A, hA⟩ := exists_holderOnWith_time_coordinate T
  obtain ⟨B, hB⟩ := exists_joint_holder g u.continuousOn_toFun
    (exists_holderOnWith_time_realization g u)
  have hD : ∃ C : ℝ≥0, HolderOnWith C (1 / 4)
      (fun t => scalarH1PiToContinuous g (spatialDerivative g (w t))) (Icc 0 T) :=
    AddCircle.exists_holderOnWith_parameterDerivativeHsPi g u w hw hproducer
  obtain ⟨C, hC⟩ := exists_joint_holder g
    ((spatialDerivative (ι := ι) g).continuous.comp_continuousOn hw) hD
  refine ⟨max A (max B C), ?_⟩
  intro p hp q hq
  change edist (p.time,
      scalarH1PiToContinuous g (u.toFun p.time) (p.space : AddCircle (1 : ℝ)),
      deriv (fun x : ℝ => scalarH1PiToContinuous g (u.toFun p.time)
        (x : AddCircle (1 : ℝ))) p.space)
    (q.time, scalarH1PiToContinuous g (u.toFun q.time) (q.space : AddCircle (1 : ℝ)),
      deriv (fun x : ℝ => scalarH1PiToContinuous g (u.toFun q.time)
        (x : AddCircle (1 : ℝ))) q.space) ≤ _
  rw [(hasDerivAt_realization g u w hproducer hp.1 p.space).deriv,
    (hasDerivAt_realization g u w hproducer hq.1 q.space).deriv]
  exact (holderOnWith_prodMk hA (holderOnWith_prodMk hB hC)) p hp q hq

theorem maximalRegularityDuhamelVectorMap_exists_holderOnWith_firstJet
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℝ) + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) T) :
    ∃ w : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 2),
      ContinuousOn w (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (show (1 : ℝ) ≤ 2 by norm_num)) (w t) =
        (maximalRegularityDuhamelVectorMap hT u₀ F).toFun t) ∧
      (w =ᵐ[timeMeasure T] fun t => ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (show (2 : ℝ) ≤ (1 : ℝ) + 2 by norm_num))
        (maximalRegularityDuhamelVectorField hT u₀ F t)) ∧
      (∀ t ∈ Icc 0 T, ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => scalarH1PiToContinuous g
          ((maximalRegularityDuhamelVectorMap hT u₀ F).toFun t)
          (y : AddCircle (1 : ℝ)))
          (scalarH1PiToContinuous g
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorHsInclusion (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num))
              (AddCircle.parameterDerivativeHsPi g 1
                (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
                  tensorHsInclusion (show ((1 : ℕ) : ℝ) + 1 ≤ 2 by norm_num)) (w t))))
            (x : AddCircle (1 : ℝ))) x) ∧
      ∃ C : ℝ≥0, HolderOnWith C (1 / 2)
        (fun p : ParabolicPoint ℝ => (p.time,
          scalarH1PiToContinuous g ((maximalRegularityDuhamelVectorMap hT u₀ F).toFun p.time)
            (p.space : AddCircle (1 : ℝ)),
          deriv (fun x : ℝ => scalarH1PiToContinuous g
            ((maximalRegularityDuhamelVectorMap hT u₀ F).toFun p.time)
            (x : AddCircle (1 : ℝ))) p.space))
        (parabolicCylinder (Icc 0 T) (Icc 0 1)) := by
  obtain ⟨w, hw, hlo, hhi, _⟩ :=
    maximalRegularityDuhamelVectorMap_exists_holderOnWith_parameterDerivative g hT u₀ F
  obtain ⟨C, hC⟩ := exists_holderOnWith_firstJet_of_timeH1 g
    (maximalRegularityDuhamelVectorMap hT u₀ F) w hw hlo
  refine ⟨w, hw, hlo, hhi, ?_, C, hC⟩
  intro t ht x
  exact hasDerivAt_realization g (maximalRegularityDuhamelVectorMap hT u₀ F) w hlo ht x

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
