import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleClassicalDerivative
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.ContinuousRepresentative

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev
open DifferentialGeometry.Analysis.Spectral

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

variable {ι : Type*} [Fintype ι]

private theorem continuousOn_scalarH1PiToContinuous_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {K : Set ℝ} {f : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 1)}
    (hf : ContinuousOn f K) :
    ContinuousOn (fun p : AddCircle (1 : ℝ) × ℝ => scalarH1PiToContinuous g (f p.2) p.1)
      (univ ×ˢ K) := by
  exact (((scalarH1PiToContinuous g).continuous.comp_continuousOn hf).comp
    continuousOn_snd (fun _ h => h.2)).eval continuousOn_fst

theorem exists_continuousOn_parameterDerivative_representative
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) T)
    (v : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℝ) + 2))) T)
    (hlink : ∀ᵐ t ∂timeMeasure T,
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (1 : ℝ) ≤ (1 : ℝ) + 2 by norm_num)) (v t) = u.toFun t) :
    ∃ d : ℝ → C(AddCircle (1 : ℝ), ι → ℝ),
      ContinuousOn (fun p : AddCircle (1 : ℝ) × ℝ =>
        scalarH1PiToContinuous g (u.toFun p.2) p.1) (univ ×ˢ Icc 0 T) ∧
      ContinuousOn d (Icc 0 T) ∧
      ContinuousOn (fun p : AddCircle (1 : ℝ) × ℝ => d p.2 p.1) (univ ×ˢ Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, ContDiff ℝ 1
        (fun x : ℝ => scalarH1PiToContinuous g (u.toFun t)
          (x : AddCircle (1 : ℝ)))) ∧
      (∀ t ∈ Icc 0 T, ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => scalarH1PiToContinuous g (u.toFun t)
          (y : AddCircle (1 : ℝ))) (d t (x : AddCircle (1 : ℝ))) x) ∧
      d =ᵐ[timeMeasure T] fun t =>
        scalarH1PiToContinuous g
          (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (g := g) (r := 0) (s := 0)
              (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
            (AddCircle.parameterDerivativeHsPi g 1
              (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
                tensorHsInclusion (g := g) (r := 0) (s := 0)
                  (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ (1 : ℝ) + 2)) (v t)))) := by
  obtain ⟨w, hw, hwlo, hwhi⟩ := exists_continuousOn_intermediate_representative hT u v hlink
  let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ (1 : ℝ) + 1))
  let D := (scalarH1PiToContinuous (ι := ι) g).comp
    ((ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))).comp
          ((AddCircle.parameterDerivativeHsPi g 1).comp L))
  have hd : ContinuousOn (fun t => D (w t)) (Icc 0 T) :=
    D.continuous.comp_continuousOn hw
  have hder : ∀ t ∈ Icc 0 T, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => scalarH1PiToContinuous g (u.toFun t)
        (y : AddCircle (1 : ℝ))) (D (w t) (x : AddCircle (1 : ℝ))) x := by
    intro t ht x
    have h := AddCircle.hasDerivAt_scalarH1PiToContinuous g (L (w t)) x
    have hlo : ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)) (L (w t)) = u.toFun t := by
      rw [← hwlo t ht]
      apply PiLp.ext
      intro i
      exact (tensorHsInclusion_trans_apply (by norm_num) (by norm_num) (w t i)).symm
    rw [hlo] at h
    exact h
  refine ⟨fun t => D (w t), continuousOn_scalarH1PiToContinuous_apply g u.continuousOn_toFun,
    hd, ?_, ?_, hder, ?_⟩
  · exact (hd.comp continuousOn_snd (fun _ h => h.2)).eval continuousOn_fst
  · intro t ht
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun x => (hder t ht x).differentiableAt, ?_⟩
    have heq := funext (fun x => (hder t ht x).deriv)
    rw [heq]
    exact (D (w t)).continuous.comp (AddCircle.continuous_mk' 1)
  · filter_upwards [hwhi] with t ht
    rw [ht]
    dsimp only [D, ContinuousLinearMap.comp_apply]
    congr 3

theorem maximalRegularityDuhamelVectorMap_exists_continuousOn_parameterDerivative
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℝ) + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) T) :
    let u := maximalRegularityDuhamelVectorMap hT u₀ F
    let v := maximalRegularityDuhamelVectorField hT u₀ F
    ∃ d : ℝ → C(AddCircle (1 : ℝ), ι → ℝ),
      ContinuousOn (fun p : AddCircle (1 : ℝ) × ℝ =>
        scalarH1PiToContinuous g (u.toFun p.2) p.1) (univ ×ˢ Icc 0 T) ∧
      ContinuousOn d (Icc 0 T) ∧
      ContinuousOn (fun p : AddCircle (1 : ℝ) × ℝ => d p.2 p.1) (univ ×ˢ Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, ContDiff ℝ 1
        (fun x : ℝ => scalarH1PiToContinuous g (u.toFun t)
          (x : AddCircle (1 : ℝ)))) ∧
      (∀ t ∈ Icc 0 T, ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => scalarH1PiToContinuous g (u.toFun t)
          (y : AddCircle (1 : ℝ))) (d t (x : AddCircle (1 : ℝ))) x) ∧
      d =ᵐ[timeMeasure T] fun t =>
        scalarH1PiToContinuous g
          (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (g := g) (r := 0) (s := 0)
              (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
            (AddCircle.parameterDerivativeHsPi g 1
              (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
                tensorHsInclusion (g := g) (r := 0) (s := 0)
                  (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ (1 : ℝ) + 2)) (v t)))) := by
  dsimp only
  apply exists_continuousOn_parameterDerivative_representative g hT
    (maximalRegularityDuhamelVectorMap hT u₀ F)
    (maximalRegularityDuhamelVectorField hT u₀ F)
  let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (1 : ℝ) ≤ (1 : ℝ) + 2 by norm_num))
  have hpin := maximalRegularityDuhamelVectorField_toFunL2 hT
    (tensorResolventL2_isCompactOperator
      (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0) u₀ F
  have ha := L.coeFn_compLpL (p := 2) (μ := timeMeasure T)
    (maximalRegularityDuhamelVectorField hT u₀ F)
  have hb := coeFn_ofContinuousOn (maximalRegularityDuhamelVectorMap hT u₀ F).continuousOn_toFun
  filter_upwards [ha, hb] with t hta htb
  change (L.compLpL 2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT u₀ F)) t = _ at hta
  change (maximalRegularityDuhamelVectorMap hT u₀ F).toFunL2 t = _ at htb
  rw [show L.compLpL 2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT u₀ F) =
    (maximalRegularityDuhamelVectorMap hT u₀ F).toFunL2 from hpin] at hta
  exact hta.symm.trans htb

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
