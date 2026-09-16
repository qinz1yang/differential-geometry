import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivativeLift
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleDifferentiation
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.Inclusion
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.ContinuousRepresentative

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open TensorHeatEquation TensorSpectral TimeSobolev
open DifferentialGeometry.Analysis.Spectral
variable {ι : Type*} [Fintype ι]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem exists_continuousOn_representative_of_parameterDerivative_forcing_lift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))) T)
    (hlift : parameterDerivativeDuhamelForcing g n hT F =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by exact_mod_cast Nat.le_succ n : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ)))).compLpL
            2 (timeMeasure T) FH) :
    ∃ w : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2)),
      ContinuousOn w (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by linarith : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 2)) (w t) =
        (maximalRegularityDuhamelVectorMap hT 0 F).toFun t) ∧
      w =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 F := by
  have hc := tensorResolventL2_isCompactOperator
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0
  obtain ⟨u, hu, hulo, hufield⟩ :=
    maximalRegularityDuhamelVectorMap_exists_continuousOn_representative hT hc 0 F
  obtain ⟨v, hv, hvlo, _⟩ :=
    maximalRegularityDuhamelVectorMap_exists_continuousOn_representative hT hc 0 FH
  let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : (n : ℝ) + 2 ≤ ((n + 1 : ℕ) : ℝ) + 1))
  have hcompat (t : ℝ) (ht : t ∈ Icc 0 T) (i : ι) :
      tensorHsInclusion (by exact_mod_cast Nat.le_succ n : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
        (AddCircle.parameterDerivativeHs g (n + 1)
          (tensorHsInclusion (by push_cast; linarith :
            ((n + 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 2) (K (u t) i))) =
      tensorHsInclusion (by linarith : (n : ℝ) ≤ (n : ℝ) + 2) (K (v t) i) := by
    have hd := (parameterDerivative_duhamel_vector_eq g n hT F).2.2 t ht
    rw [hlift] at hd
    have hvmap := maximalRegularityDuhamelVectorMap_toFun_tensorHsInclusion
      (by exact_mod_cast Nat.le_succ n : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ)) hT hc 0 FH ht
    rw [map_zero] at hvmap
    rw [← hvmap, ← hulo t ht, ← hvlo t ht] at hd
    have hdi := congrArg (fun z => z i) hd
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.piLpMap_apply,
      AddCircle.parameterDerivativeHsPi_apply, ← tensorHsInclusion_trans_apply] at hdi
    simp only [K, ContinuousLinearMap.piLpMap_apply, ← tensorHsInclusion_trans_apply]
    have hcomm := AddCircle.parameterDerivativeHs_tensorHsInclusion g (Nat.le_succ n) (u t i)
    rw [← hdi] at hcomm
    exact hcomm.symm
  obtain ⟨w, hw, hwlo⟩ := AddCircle.exists_continuousOn_tensorHsInclusion_eq_of_parameterDerivative_lift
    g n (σ := n) (by exact_mod_cast Nat.le_succ n) (fun t => K (u t)) (fun t => K (v t))
      (K.continuous.comp_continuousOn hu) (K.continuous.comp_continuousOn hv) hcompat
  refine ⟨w, hw, ?_, ?_⟩
  · intro t ht
    have h := hwlo t ht
    apply PiLp.ext
    intro i
    have hi := congrArg (fun z => z i) h
    have hu := congrArg (fun z => z i) (hulo t ht)
    simp only [K, ContinuousLinearMap.piLpMap_apply] at hi hu ⊢
    rw [← hu]
    apply tensorHsInclusion_injective
      (by push_cast; linarith : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
    simp only [← tensorHsInclusion_trans_apply]
    have hi' := congrArg (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (n : ℝ) ≤ (n : ℝ) + 2)) hi
    simpa only [← tensorHsInclusion_trans_apply] using hi'
  · filter_upwards [hufield, ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht hmem
    have h := hwlo t hmem
    rw [ht] at h
    apply PiLp.ext
    intro i
    apply tensorHsInclusion_injective (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : (n : ℝ) + 2 ≤ ((n + 1 : ℕ) : ℝ) + 2)
    have hi := congrArg (fun z => z i) h
    simpa only [K, ContinuousLinearMap.piLpMap_apply,
      ← tensorHsInclusion_trans_apply] using hi

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
