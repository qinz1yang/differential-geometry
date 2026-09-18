import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.RepresentativeDependence
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleIteratedDerivativeNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleIteratedDerivativeLift
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleIteratedDifferentiation
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

private def iteratedDerivativeFieldMap
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((0 + 2 : ℕ) : ℝ))).comp
        ((AddCircle.iteratedParameterDerivativeHs g (0 + 2) m).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith :
              ((0 + 2 + m : ℕ) : ℝ) ≤ (m : ℝ) + 2))))

private def iteratedDerivativeFieldProjection
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ (1 : ℝ) + 2))

private def iteratedDerivativeStateNormalization
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 + 1 + m : ℕ) : ℝ)) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((1 + 1 + m : ℕ) : ℝ) ≤ (m : ℝ) + 2))

private def iteratedDerivativeLiftNormalization
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 + 2 : ℕ) : ℝ)) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 + 2 : ℕ) : ℝ) ≤ (1 : ℝ) + 2))

private def iteratedDerivativeReconstructionProjection
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 + 2 + m : ℕ) : ℝ)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 + 1 + m : ℕ) : ℝ)) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 + 1 + m ≤ 1 + 2 + m by omega) :
        ((1 + 1 + m : ℕ) : ℝ) ≤ ((1 + 2 + m : ℕ) : ℝ)))

private def iteratedDerivativeReconstructionNormalization
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 + 2 + m : ℕ) : ℝ)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3)) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : (m : ℝ) + 3 ≤ ((1 + 2 + m : ℕ) : ℝ)))

private def iteratedDerivativeRegularityProjection
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (m : ℝ) + 2 ≤ (m : ℝ) + 3))

private theorem iteratedDerivative_field_ae_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ)
    {T : ℝ}
    (U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2))) T)
    (V : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℝ) + 2))) T) :
  let Dh := iteratedDerivativeFieldMap (ι := ι) g m
  let J := iteratedDerivativeFieldProjection (ι := ι) g
  let A := iteratedDerivativeStateNormalization (ι := ι) g m
  let B := iteratedDerivativeLiftNormalization (ι := ι) g
  let U' := A.compLpL 2 (timeMeasure T) U
  let V' := B.compLpL 2 (timeMeasure T) V
  Dh.compLpL 2 (timeMeasure T) U = J.compLpL 2 (timeMeasure T) V →
  ∀ᵐ t ∂timeMeasure T, ∀ i : ι,
      tensorHsInclusion (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 + 1 : ℕ) : ℝ))
        (AddCircle.iteratedParameterDerivativeHs g (1 + 1) m (U' t i)) =
      tensorHsInclusion (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 + 2 : ℕ) : ℝ)) (V' t i) := by
  intro Dh J A B U' V' hfield
  filter_upwards [Dh.coeFn_compLpL U, J.coeFn_compLpL V,
    A.coeFn_compLpL U, B.coeFn_compLpL V] with t hDh hJ hA hB
  have ht : Dh (U t) = J (V t) := by
    rw [← hDh, ← hJ]
    exact congrArg (fun z : timeL2
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2))) T => z t) hfield
  intro i
  dsimp only [U', V']
  rw [hA, hB]
  have hi := congrArg (fun z => z i) ht
  simpa only [Dh, iteratedDerivativeFieldMap, J, iteratedDerivativeFieldProjection, A,
      iteratedDerivativeStateNormalization, B, iteratedDerivativeLiftNormalization,
      ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.piLpMap_apply, ← tensorHsInclusion_trans_apply] using hi

private theorem iteratedDerivativeRegularityProjection_compLpL_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ)
    {T : ℝ}
    (U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2))) T)
    (W : timeL2 (PiLp 2 (fun _ : ι =>
      TensorHs g 0 0 ((1 + 2 + m : ℕ) : ℝ))) T) :
  let K := iteratedDerivativeReconstructionProjection (ι := ι) g m
  let L := iteratedDerivativeReconstructionNormalization (ι := ι) g m
  let R := iteratedDerivativeRegularityProjection (ι := ι) g m
  let A := iteratedDerivativeStateNormalization (ι := ι) g m
  K.compLpL 2 (timeMeasure T) W = A.compLpL 2 (timeMeasure T) U →
    R.compLpL 2 (timeMeasure T) (L.compLpL 2 (timeMeasure T) W) = U := by
  intro K L R A hW
  apply Lp.ext
  filter_upwards [R.coeFn_compLpL (L.compLpL 2 (timeMeasure T) W),
    L.coeFn_compLpL W, K.coeFn_compLpL W, A.coeFn_compLpL U] with t hR hL hK hA
  rw [hR, hL]
  apply PiLp.ext
  intro i
  apply tensorHsInclusion_injective (g := g) (r := 0) (s := 0)
    (by push_cast; linarith : ((1 + 1 + m : ℕ) : ℝ) ≤ (m : ℝ) + 2)
  have ht : K (W t) = A (U t) := by
    rw [← hK, hW]
    exact hA
  have hi := congrArg (fun z => z i) ht
  simpa only [R, iteratedDerivativeRegularityProjection, L,
      iteratedDerivativeReconstructionNormalization, K, iteratedDerivativeReconstructionProjection,
      A, iteratedDerivativeStateNormalization, ContinuousLinearMap.piLpMap_apply,
    ← tensorHsInclusion_trans_apply] using hi


private theorem exists_timeL2_tensorHsInclusion_eq_of_iteratedParameterDerivative_field_lift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ)
    {T : ℝ}
    (U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2))) T)
    (V : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℝ) + 2))) T) :
  let Dh := iteratedDerivativeFieldMap (ι := ι) g m
  let J := iteratedDerivativeFieldProjection (ι := ι) g
  Dh.compLpL 2 (timeMeasure T) U = J.compLpL 2 (timeMeasure T) V →
    ∃ w : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3))) T,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by linarith : (m : ℝ) + 2 ≤ (m : ℝ) + 3))).compLpL
            2 (timeMeasure T) w = U := by
  intro Dh J hfield
  let A := iteratedDerivativeStateNormalization (ι := ι) g m
  let B := iteratedDerivativeLiftNormalization (ι := ι) g
  let U' := A.compLpL 2 (timeMeasure T) U
  let V' := B.compLpL 2 (timeMeasure T) V
  have hcompat := iteratedDerivative_field_ae_eq g m U V hfield
  obtain ⟨W, hW⟩ :=
    AddCircle.exists_timeL2_tensorHsInclusion_eq_of_iteratedParameterDerivative_lift
      g 1 m (σ := ((0 : ℕ) : ℝ) + 2) (by norm_num) U' V' hcompat
  let L := iteratedDerivativeReconstructionNormalization (ι := ι) g m
  refine ⟨L.compLpL 2 (timeMeasure T) W, ?_⟩
  exact iteratedDerivativeRegularityProjection_compLpL_eq g m U W hW

theorem exists_timeL2_tensorHsInclusion_eq_of_iteratedParameterDerivative_forcing_lift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T)
    (FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 : ℝ))) T)
    (hlift : iteratedParameterDerivativeDuhamelForcing g 0 m hT F =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) ≤ (1 : ℝ)))).compLpL 2 (timeMeasure T) FH) :
    ∃ w : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3))) T,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by linarith : (m : ℝ) + 2 ≤ (m : ℝ) + 3))).compLpL
            2 (timeMeasure T) w = maximalRegularityDuhamelVectorField hT 0 F := by
  let U := maximalRegularityDuhamelVectorField hT 0 F
  let V := maximalRegularityDuhamelVectorField hT 0 FH
  let Dh := iteratedDerivativeFieldMap (ι := ι) g m
  let J := iteratedDerivativeFieldProjection (ι := ι) g
  have hderiv := (iteratedParameterDerivative_duhamel_vector_eq g 0 m hT F).1
  change Dh.compLpL 2 (timeMeasure T) U =
    maximalRegularityDuhamelVectorField hT 0
      (iteratedParameterDerivativeDuhamelForcing g 0 m hT F) at hderiv
  have hnat : J.compLpL 2 (timeMeasure T) V =
      maximalRegularityDuhamelVectorField hT 0
        (iteratedParameterDerivativeDuhamelForcing g 0 m hT F) := by
    rw [hlift]
    simpa only [map_zero, J, iteratedDerivativeFieldProjection, V] using
      maximalRegularityDuhamelVectorField_compLpL_tensorHsInclusion
        (by norm_num : ((0 : ℕ) : ℝ) ≤ (1 : ℝ)) hT
        (tensorResolventL2_isCompactOperator g 0 0) 0 FH
  have hfield := hderiv.trans hnat.symm
  exact exists_timeL2_tensorHsInclusion_eq_of_iteratedParameterDerivative_field_lift
    g m U V hfield

theorem exists_continuousOn_representative_of_iteratedParameterDerivative_forcing_lift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T)
    (FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 : ℝ))) T)
    (hlift : iteratedParameterDerivativeDuhamelForcing g 0 m hT F =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) ≤ (1 : ℝ)))).compLpL 2 (timeMeasure T) FH) :
    ∃ w : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)),
      ContinuousOn w (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by linarith : (m : ℝ) ≤ (m : ℝ) + 2)) (w t) =
        (maximalRegularityDuhamelVectorMap hT 0 F).toFun t) ∧
      w =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 F := by
  have hc := tensorResolventL2_isCompactOperator
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0
  obtain ⟨u, hu, hulo, hufield⟩ :=
    maximalRegularityDuhamelVectorMap_exists_continuousOn_representative hT hc 0 F
  obtain ⟨v, hv, hvlo, _⟩ :=
    maximalRegularityDuhamelVectorMap_exists_continuousOn_representative hT hc 0 FH
  let K₁ := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((0 + 1 + m : ℕ) : ℝ) ≤ (m : ℝ) + 1))
  let K₂ := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 + 2 : ℕ) : ℝ) ≤ (1 : ℝ) + 1))
  have hulo' (t : ℝ) (ht : t ∈ Icc 0 T) :
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith : (m : ℝ) ≤ ((0 + 1 + m : ℕ) : ℝ))) (K₁ (u t)) =
        (maximalRegularityDuhamelVectorMap hT 0 F).toFun t := by
    apply PiLp.ext
    intro i
    have hi := congrArg (fun z => z i) (hulo t ht)
    simpa only [K₁, ContinuousLinearMap.piLpMap_apply,
      ← tensorHsInclusion_trans_apply] using hi
  have hvlo' (t : ℝ) (ht : t ∈ Icc 0 T) :
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((0 + 2 : ℕ) : ℝ))) (K₂ (v t)) =
        (maximalRegularityDuhamelVectorMap hT 0 FH).toFun t := by
    apply PiLp.ext
    intro i
    have hi := congrArg (fun z => z i) (hvlo t ht)
    simpa only [K₂, ContinuousLinearMap.piLpMap_apply,
      ← tensorHsInclusion_trans_apply] using hi
  have hcompat (t : ℝ) (ht : t ∈ Icc 0 T) (i : ι) :
      tensorHsInclusion (by norm_num : ((0 : ℕ) : ℝ) ≤ ((0 + 1 : ℕ) : ℝ))
        (AddCircle.iteratedParameterDerivativeHs g (0 + 1) m (K₁ (u t) i)) =
      tensorHsInclusion (by norm_num : ((0 : ℕ) : ℝ) ≤ ((0 + 2 : ℕ) : ℝ)) (K₂ (v t) i) := by
    have hd := (iteratedParameterDerivative_duhamel_vector_eq g 0 m hT F).2.2 t ht
    rw [hlift] at hd
    have hvmap := maximalRegularityDuhamelVectorMap_toFun_tensorHsInclusion
      (by norm_num : ((0 : ℕ) : ℝ) ≤ (1 : ℝ)) hT hc 0 FH ht
    rw [map_zero] at hvmap
    rw [← hvmap, ← hulo' t ht, ← hvlo' t ht] at hd
    have hdi := congrArg (fun z => z i) hd
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.piLpMap_apply,
      ← tensorHsInclusion_trans_apply] at hdi
    have hcomm := AddCircle.iteratedParameterDerivativeHs_tensorHsInclusion g
      (by decide : 0 ≤ 1) m (K₁ (u t) i)
    exact hcomm.symm.trans hdi.symm
  obtain ⟨W, hW, hWlo⟩ :=
    AddCircle.exists_continuousOn_tensorHsInclusion_eq_of_iteratedParameterDerivative_lift
      g 0 m (σ := ((0 : ℕ) : ℝ)) (by norm_num) (fun t => K₁ (u t)) (fun t => K₂ (v t))
        (K₁.continuous.comp_continuousOn hu) (K₂.continuous.comp_continuousOn hv) hcompat
  let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : (m : ℝ) + 2 ≤ ((0 + 2 + m : ℕ) : ℝ)))
  refine ⟨fun t => L (W t), L.continuous.comp_continuousOn hW, ?_, ?_⟩
  · intro t ht
    apply PiLp.ext
    intro i
    have hi := congrArg (fun z => z i) (hWlo t ht)
    have hp := congrArg (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : (m : ℝ) ≤ ((0 + 1 + m : ℕ) : ℝ))) hi
    have hu' := congrArg (fun z => z i) (hulo' t ht)
    simp only [L, ContinuousLinearMap.piLpMap_apply,
      ← tensorHsInclusion_trans_apply] at hp hu' ⊢
    exact hp.trans hu'
  · filter_upwards [hufield, ae_restrict_mem (μ := volume) measurableSet_Icc]
      with t ht hmem
    apply PiLp.ext
    intro i
    apply tensorHsInclusion_injective (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((0 + 1 + m : ℕ) : ℝ) ≤ (m : ℝ) + 2)
    have hi := congrArg (fun z => z i) (hWlo t hmem)
    rw [ht] at hi
    simpa only [L, K₁, ContinuousLinearMap.piLpMap_apply,
      ← tensorHsInclusion_trans_apply] using hi

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

noncomputable section

open Filter MeasureTheory
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity
open DifferentialGeometry.Analysis.Spectral

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private local instance vectorTensorHsNormedSpace
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (a : ℝ) :
    NormedSpace ℝ (PiLp 2 (fun _ : ι => TensorHs g 0 0 a)) := inferInstance

private def stateInclusion {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
  (g := g) (r := 0) (s := 0)
    (by linarith : (m : ℝ) + 2 ≤ (m : ℝ) + 3))

private def derivativeInclusion {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
  (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ (1 : ℝ) + 2))

private def highDerivative {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
  (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) + 2 ≤ ((3 : ℕ) : ℝ))).comp
      ((AddCircle.iteratedParameterDerivativeHs g 3 m).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith : ((3 + m : ℕ) : ℝ) ≤ (m : ℝ) + 3))))

private def lowDerivative {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
  (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))).comp
      ((AddCircle.iteratedParameterDerivativeHs g 2 m).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith : ((2 + m : ℕ) : ℝ) ≤ (m : ℝ) + 2))))

private theorem iteratedDerivative_duhamel_field_projection
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T)
    (FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 : ℝ))) T)
    (hlift : iteratedParameterDerivativeDuhamelForcing g 0 m hT F =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ 1))).compLpL
          2 (timeMeasure T) FH) :
    (lowDerivative (ι := ι) g m).compLpL 2 (timeMeasure T)
        (maximalRegularityDuhamelVectorField hT 0 F) =
      (derivativeInclusion (ι := ι) g).compLpL 2 (timeMeasure T)
        (maximalRegularityDuhamelVectorField hT 0 FH) := by
  let D := lowDerivative (ι := ι) g m
  let J := derivativeInclusion (ι := ι) g
  have hderiv := (iteratedParameterDerivative_duhamel_vector_eq g 0 m hT F).1
  change D.compLpL 2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 F) =
    maximalRegularityDuhamelVectorField hT 0
      (iteratedParameterDerivativeDuhamelForcing g 0 m hT F) at hderiv
  have hnat : J.compLpL 2 (timeMeasure T)
      (maximalRegularityDuhamelVectorField hT 0 FH) =
    maximalRegularityDuhamelVectorField hT 0
      (iteratedParameterDerivativeDuhamelForcing g 0 m hT F) := by
    rw [hlift]
    simpa only [map_zero, J, derivativeInclusion] using
      maximalRegularityDuhamelVectorField_compLpL_tensorHsInclusion
        (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ 1) hT
        (tensorResolventL2_isCompactOperator g 0 0) 0 FH
  exact hderiv.trans hnat.symm

private theorem derivative_comp_stateInclusion
    {ι : Type*} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) :
    (lowDerivative (ι := ι) g m).comp (stateInclusion g m) =
      (derivativeInclusion g).comp (highDerivative g m) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  have hn := AddCircle.iteratedParameterDerivativeHs_tensorHsInclusion g
    (by decide : 2 ≤ 3) m
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((3 + m : ℕ) : ℝ) ≤ (m : ℝ) + 3) (x i))
  have hn' := congrArg (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))) hn
  simpa only [lowDerivative, stateInclusion, derivativeInclusion, highDerivative,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.piLpMap_apply,
    ← tensorHsInclusion_trans_apply,
    tensorHsInclusion_refl_apply] using hn'

private theorem derivativeInclusion_injective
    {ι : Type*} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    Function.Injective (derivativeInclusion (ι := ι) g) := by
  intro x y hxy
  apply PiLp.ext
  intro i
  exact tensorHsInclusion_injective
    (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ (1 : ℝ) + 2) (congrArg (fun v => v i) hxy)

private theorem compLpL_eq_of_injective_commutation
    {X Y Z Q : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {T : ℝ} (K : X →L[ℝ] Y) (D : Y →L[ℝ] Q) (J : Z →L[ℝ] Q) (H : X →L[ℝ] Z)
    (hJ : Function.Injective J) (hcomm : D.comp K = J.comp H)
    (V : timeL2 X T) (U : timeL2 Z T)
    (hfield : D.compLpL 2 (timeMeasure T) (K.compLpL 2 (timeMeasure T) V) =
      J.compLpL 2 (timeMeasure T) U) : H.compLpL 2 (timeMeasure T) V = U := by
  apply Lp.ext
  filter_upwards [H.coeFn_compLpL V,
    D.coeFn_compLpL (K.compLpL 2 (timeMeasure T) V), K.coeFn_compLpL V,
    J.coeFn_compLpL U] with t hH hD hK hJU
  rw [hH]
  apply hJ
  have heq : D (K (V t)) = J (U t) := by
    rw [← hK, ← hD, hfield, hJU]
  have hc := DFunLike.congr_fun hcomm (V t)
  exact hc.symm.trans heq

private theorem iteratedDerivative_high_field_eq
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T)
    (FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 : ℝ))) T)
    (V : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3))) T)
    (hlift : iteratedParameterDerivativeDuhamelForcing g 0 m hT F =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ 1))).compLpL
          2 (timeMeasure T) FH)
    (hV : (stateInclusion (ι := ι) g m).compLpL 2 (timeMeasure T) V =
      maximalRegularityDuhamelVectorField hT 0 F) :
    (highDerivative (ι := ι) g m).compLpL 2 (timeMeasure T) V =
      maximalRegularityDuhamelVectorField hT 0 FH := by
  exact compLpL_eq_of_injective_commutation
    (stateInclusion (ι := ι) g m) (lowDerivative g m) (derivativeInclusion g)
    (highDerivative g m) (derivativeInclusion_injective g)
    (derivative_comp_stateInclusion g m) V (maximalRegularityDuhamelVectorField hT 0 FH)
    ((congrArg ((lowDerivative (ι := ι) g m).compLpL 2 (timeMeasure T)) hV).trans
      (iteratedDerivative_duhamel_field_projection g m hT F FH hlift))

theorem iteratedParameterDerivativeHs_duhamel_field_of_lift
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T)
    (FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 : ℝ))) T)
    (V : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3))) T)
    (hlift : iteratedParameterDerivativeDuhamelForcing g 0 m hT F =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ 1))).compLpL
          2 (timeMeasure T) FH)
    (hV : (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by linarith : (m : ℝ) + 2 ≤ (m : ℝ) + 3))).compLpL
          2 (timeMeasure T) V = maximalRegularityDuhamelVectorField hT 0 F) :
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) + 2 ≤ ((3 : ℕ) : ℝ))).comp
          ((AddCircle.iteratedParameterDerivativeHs g 3 m).comp
            (tensorHsInclusion (g := g) (r := 0) (s := 0)
              (by push_cast; linarith : ((3 + m : ℕ) : ℝ) ≤ (m : ℝ) + 3))))).compLpL
                2 (timeMeasure T) V = maximalRegularityDuhamelVectorField hT 0 FH := by
  exact iteratedDerivative_high_field_eq g m hT F FH V hlift hV

theorem iteratedParameterDerivativeHs_duhamel_representative_ae_of_lift
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T)
    (FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 : ℝ))) T)
    (W : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)))
    (hlift : iteratedParameterDerivativeDuhamelForcing g 0 m hT F =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ 1))).compLpL
          2 (timeMeasure T) FH)
    (hW : W =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 F) :
    (fun t => (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))).comp
          ((AddCircle.iteratedParameterDerivativeHs g 2 m).comp
            (tensorHsInclusion (g := g) (r := 0) (s := 0)
              (by push_cast; linarith : ((2 + m : ℕ) : ℝ) ≤ (m : ℝ) + 2))))) (W t))
      =ᵐ[timeMeasure T] fun t =>
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ (1 : ℝ) + 2)))
              (maximalRegularityDuhamelVectorField hT 0 FH t) := by
  let D := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))).comp
        ((AddCircle.iteratedParameterDerivativeHs g 2 m).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((2 + m : ℕ) : ℝ) ≤ (m : ℝ) + 2))))
  let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ (1 : ℝ) + 2))
  have hfield := iteratedDerivative_duhamel_field_projection g m hT F FH hlift
  change D.compLpL 2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 F) =
    J.compLpL 2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 FH) at hfield
  filter_upwards [hW, D.coeFn_compLpL (maximalRegularityDuhamelVectorField hT 0 F),
    J.coeFn_compLpL (maximalRegularityDuhamelVectorField hT 0 FH)] with t ht hD hJ
  change D (W t) = J (maximalRegularityDuhamelVectorField hT 0 FH t)
  rw [ht, ← hD, hfield, hJ]

open scoped _root_.Topology

private theorem tendstoUniformlyOn_iterated_graph
    {ι P : Type*} [Finite ι] {l : Filter P}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) (T : ℝ)
    (W₀ : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)))
    (W : P → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2))) :
  let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by linarith : (m : ℝ) + 1 ≤ (m : ℝ) + 2))
  let D := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))).comp
        ((AddCircle.iteratedParameterDerivativeHs g 2 m).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((2 + m : ℕ) : ℝ) ≤ (m : ℝ) + 2))))
  TendstoUniformlyOn (fun p t => J (W p t)) (fun t => J (W₀ t))
    l (Set.Icc (0 : ℝ) T) →
  TendstoUniformlyOn (fun p t => D (W p t)) (fun t => D (W₀ t))
    l (Set.Icc (0 : ℝ) T) →
  TendstoUniformlyOn W W₀ l (Set.Icc (0 : ℝ) T) := by
  let _ := Fintype.ofFinite ι
  intro J D hJ hD
  let A := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((0 + 2 + m : ℕ) : ℝ) ≤ (m : ℝ) + 2))
  let B := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : (m : ℝ) + 2 ≤ ((0 + 2 + m : ℕ) : ℝ)))
  let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((0 + 1 + m : ℕ) : ℝ) ≤ (m : ℝ) + 1))
  let E := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 + 2 : ℕ) : ℝ) ≤ (1 : ℝ) + 1))
  let JN := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 0 + 1 + m ≤ 0 + 2 + m by omega) :
        ((0 + 1 + m : ℕ) : ℝ) ≤ ((0 + 2 + m : ℕ) : ℝ)))
  let DN := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    AddCircle.iteratedParameterDerivativeHs g (0 + 2) m)
  have hJNorm (x : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2))) :
      JN (A x) = L (J x) := by
    apply PiLp.ext
    intro i
    simp only [JN, A, L, J, ContinuousLinearMap.piLpMap_apply,
      ← tensorHsInclusion_trans_apply]
  have hDNorm (x : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2))) :
      DN (A x) = E (D x) := by
    apply PiLp.ext
    intro i
    simp only [DN, A, E, D, ContinuousLinearMap.piLpMap_apply,
      ContinuousLinearMap.comp_apply, ← tensorHsInclusion_trans_apply,
      tensorHsInclusion_refl_apply]
  have hJ' := L.uniformContinuous.comp_tendstoUniformlyOn hJ
  have hD' := E.uniformContinuous.comp_tendstoUniformlyOn hD
  have hA : TendstoUniformlyOn (fun p t => A (W p t)) (fun t => A (W₀ t))
      l (Set.Icc (0 : ℝ) T) := by
    apply AddCircle.tendstoUniformlyOn_of_tensorHsInclusion_of_iteratedParameterDerivativeHs
      g 0 m (fun t => A (W₀ t)) (fun p t => A (W p t))
    · change TendstoUniformlyOn (fun p t => JN (A (W p t)))
        (fun t => JN (A (W₀ t))) l (Set.Icc (0 : ℝ) T)
      simpa only [Function.comp_def, hJNorm] using hJ'
    · change TendstoUniformlyOn (fun p t => DN (A (W p t)))
        (fun t => DN (A (W₀ t))) l (Set.Icc (0 : ℝ) T)
      simpa only [Function.comp_def, hDNorm] using hD'
  have hBA (x : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2))) :
      B (A x) = x := by
    apply PiLp.ext
    intro i
    simp only [A, B, ContinuousLinearMap.piLpMap_apply,
      ← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply]
  simpa only [Function.comp_def, hBA] using B.uniformContinuous.comp_tendstoUniformlyOn hA

theorem tendstoUniformlyOn_duhamel_representatives_of_iterated_forcing_lift
    {ι P : Type*} [Fintype ι] {l : Filter P}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T)
    (F : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T)
    (FH₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 : ℝ))) T)
    (FH : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 : ℝ))) T)
    (W₀ : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)))
    (W : P → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)))
    (hW₀ : ContinuousOn W₀ (Set.Icc (0 : ℝ) T))
    (hW : ∀ p, ContinuousOn (W p) (Set.Icc (0 : ℝ) T))
    (hlift₀ : iteratedParameterDerivativeDuhamelForcing g 0 m hT F₀ =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ 1))).compLpL
          2 (timeMeasure T) FH₀)
    (hlift : ∀ p, iteratedParameterDerivativeDuhamelForcing g 0 m hT (F p) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ 1))).compLpL
          2 (timeMeasure T) (FH p))
    (hpin₀ : W₀ =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 F₀)
    (hpin : ∀ p, W p =ᵐ[timeMeasure T]
      maximalRegularityDuhamelVectorField hT 0 (F p))
    (hJ : TendstoUniformlyOn (fun p t =>
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by linarith : (m : ℝ) + 1 ≤ (m : ℝ) + 2))) (W p t))
      (fun t => (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by linarith : (m : ℝ) + 1 ≤ (m : ℝ) + 2))) (W₀ t))
      l (Set.Icc (0 : ℝ) T))
    (hFH : Tendsto FH l (𝓝 FH₀)) :
    TendstoUniformlyOn W W₀ l (Set.Icc (0 : ℝ) T) := by
  let D := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))).comp
        ((AddCircle.iteratedParameterDerivativeHs g 2 m).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((2 + m : ℕ) : ℝ) ≤ (m : ℝ) + 2))))
  have hpinD (f : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T)
      (fh : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 : ℝ))) T)
      (w : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)))
      (hliftf : iteratedParameterDerivativeDuhamelForcing g 0 m hT f =
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ 1))).compLpL
            2 (timeMeasure T) fh)
      (hpinw : w =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 f) :
      (fun t => D (w t)) =ᵐ[timeMeasure T] fun t =>
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by linarith : (1 : ℝ) + 1 ≤ (1 : ℝ) + 2)))
              (maximalRegularityDuhamelVectorField hT 0 fh t) := by
    filter_upwards [iteratedParameterDerivativeHs_duhamel_representative_ae_of_lift
      g m hT f fh w hliftf hpinw] with t ht
    apply PiLp.ext
    intro i
    apply tensorHsInclusion_injective
      (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ (1 : ℝ) + 1)
    simpa only [D, ContinuousLinearMap.piLpMap_apply, ContinuousLinearMap.comp_apply,
      ← tensorHsInclusion_trans_apply] using congrArg (fun v => v i) ht
  have hD : TendstoUniformlyOn (fun p t => D (W p t)) (fun t => D (W₀ t))
      l (Set.Icc (0 : ℝ) T) :=
    tendstoUniformlyOn_continuousOn_duhamel_representatives hT FH₀ FH
      (fun t => D (W₀ t)) (fun p t => D (W p t))
      (D.continuous.comp_continuousOn hW₀)
      (fun p => D.continuous.comp_continuousOn (hW p))
      (hpinD F₀ FH₀ W₀ hlift₀ hpin₀)
      (fun p => hpinD (F p) (FH p) (W p) (hlift p) (hpin p)) hFH
  exact tendstoUniformlyOn_iterated_graph g m T W₀ W hJ hD

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end

noncomputable section

open Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem tendsto_duhamel_zero
    {ι P : Type*} [Fintype ι] {l : Filter P}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {a T : ℝ} (hT : 0 < T)
    (F₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 a)) T)
    (F : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 a)) T)
    (hF : Tendsto F l (𝓝 F₀)) :
    Tendsto (fun p => maximalRegularityDuhamelVectorField hT 0 (F p)) l
      (𝓝 (maximalRegularityDuhamelVectorField hT 0 F₀)) := by
  let S := maximalRegularityVectorFieldL (ι := ι) (g := g) (r := 0) (s := 0) a hT.le
  have hS : Tendsto (fun p => S (F p)) l (𝓝 (S F₀)) :=
    (S.continuous.tendsto F₀).comp hF
  have heq (f : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 a)) T) :
      S f = maximalRegularityDuhamelVectorField hT 0 f :=
    maximalRegularityVectorFieldL_eq_duhamel hT f
  simpa only [heq] using hS

private theorem tendsto_compLpL
    {X Y P : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {l : Filter P} {T : ℝ}
    (A : X →L[ℝ] Y) (f₀ : timeL2 X T) (f : P → timeL2 X T)
    (hf : Tendsto f l (𝓝 f₀)) :
    Tendsto (fun p => A.compLpL 2 (timeMeasure T) (f p)) l
      (𝓝 (A.compLpL 2 (timeMeasure T) f₀)) :=
  ((A.compLpL 2 (timeMeasure T)).continuous.tendsto f₀).comp hf

private theorem compLpL_commutation
    {X Y Z Q : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] {T : ℝ}
    (A : X →L[ℝ] Y) (B : Y →L[ℝ] Z) (C : X →L[ℝ] Q) (D : Q →L[ℝ] Z)
    (h : ∀ x, B (A x) = D (C x)) (f : timeL2 X T) :
    B.compLpL 2 (timeMeasure T) (A.compLpL 2 (timeMeasure T) f) =
      D.compLpL 2 (timeMeasure T) (C.compLpL 2 (timeMeasure T) f) := by
  apply Lp.ext
  filter_upwards [B.coeFn_compLpL (A.compLpL 2 (timeMeasure T) f),
    A.coeFn_compLpL f, D.coeFn_compLpL (C.compLpL 2 (timeMeasure T) f),
    C.coeFn_compLpL f] with t hB hA hD hC
  rw [hB, hA, hD, hC]
  exact h (f t)

private theorem compLpL_leftInverse
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {T : ℝ}
    (A : X →L[ℝ] Y) (B : Y →L[ℝ] X) (h : ∀ x, B (A x) = x)
    (f : timeL2 X T) :
    B.compLpL 2 (timeMeasure T) (A.compLpL 2 (timeMeasure T) f) = f := by
  apply Lp.ext
  filter_upwards [B.coeFn_compLpL (A.compLpL 2 (timeMeasure T) f),
    A.coeFn_compLpL f] with t hB hA
  rw [hB, hA]
  exact h (f t)

private def stateProjection {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by linarith : (m : ℝ) + 2 ≤ (m : ℝ) + 3))

private def stateDerivative {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) + 2 ≤ ((3 : ℕ) : ℝ))).comp
        ((AddCircle.iteratedParameterDerivativeHs g 3 m).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((3 + m : ℕ) : ℝ) ≤ (m : ℝ) + 3))))

private def stateNormalization {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((1 + 2 + m : ℕ) : ℝ) ≤ (m : ℝ) + 3))

private def stateDenormalization {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : (m : ℝ) + 3 ≤ ((1 + 2 + m : ℕ) : ℝ)))

private def projectionNormalization {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((1 + 1 + m : ℕ) : ℝ) ≤ (m : ℝ) + 2))

private def derivativeNormalization {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 + 2 : ℕ) : ℝ) ≤ (1 : ℝ) + 2))

private def naturalStateProjection {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 + 1 + m ≤ 1 + 2 + m by omega) :
        ((1 + 1 + m : ℕ) : ℝ) ≤ ((1 + 2 + m : ℕ) : ℝ)))

private def naturalStateDerivative {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    AddCircle.iteratedParameterDerivativeHs g (1 + 2) m)

private theorem projectionNormalization_compLpL
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) (T : ℝ)
    (x : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3))) T) :
    (naturalStateProjection (ι := ι) g m).compLpL 2 (timeMeasure T)
        ((stateNormalization (ι := ι) g m).compLpL 2 (timeMeasure T) x) =
      (projectionNormalization (ι := ι) g m).compLpL 2 (timeMeasure T)
        ((stateProjection (ι := ι) g m).compLpL 2 (timeMeasure T) x) := by
  refine compLpL_commutation (T := T) (stateNormalization (ι := ι) g m)
    (naturalStateProjection (ι := ι) g m)
    (stateProjection (ι := ι) g m) (projectionNormalization (ι := ι) g m) ?_ x
  intro y
  apply PiLp.ext
  intro i
  simp only [naturalStateProjection, stateNormalization, projectionNormalization,
    stateProjection, ContinuousLinearMap.piLpMap_apply, ← tensorHsInclusion_trans_apply]

private theorem derivativeNormalization_compLpL
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) (T : ℝ)
    (x : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3))) T) :
    (naturalStateDerivative (ι := ι) g m).compLpL 2 (timeMeasure T)
        ((stateNormalization (ι := ι) g m).compLpL 2 (timeMeasure T) x) =
      (derivativeNormalization (ι := ι) g).compLpL 2 (timeMeasure T)
        ((stateDerivative (ι := ι) g m).compLpL 2 (timeMeasure T) x) := by
  refine compLpL_commutation (T := T) (stateNormalization (ι := ι) g m)
    (naturalStateDerivative (ι := ι) g m)
    (stateDerivative (ι := ι) g m) (derivativeNormalization (ι := ι) g) ?_ x
  intro y
  apply PiLp.ext
  intro i
  simp only [naturalStateDerivative, stateNormalization, derivativeNormalization,
    stateDerivative, ContinuousLinearMap.piLpMap_apply, ContinuousLinearMap.comp_apply,
    ← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply]

private theorem stateDenormalization_compLpL
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) (T : ℝ)
    (x : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3))) T) :
    (stateDenormalization (ι := ι) g m).compLpL 2 (timeMeasure T)
      ((stateNormalization (ι := ι) g m).compLpL 2 (timeMeasure T) x) = x := by
  refine compLpL_leftInverse (T := T) (stateNormalization (ι := ι) g m)
    (stateDenormalization (ι := ι) g m) ?_ x
  intro y
  apply PiLp.ext
  intro i
  simp only [stateDenormalization, stateNormalization, ContinuousLinearMap.piLpMap_apply,
    ← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply]

private theorem tendsto_normalized_graph
    {ι P : Type*} [Fintype ι] {l : Filter P}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) (T : ℝ)
    (W₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 + 2 + m : ℕ) : ℝ))) T)
    (W : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 + 2 + m : ℕ) : ℝ))) T) :
    let J := (naturalStateProjection (ι := ι) g m).compLpL 2 (timeMeasure T)
    let D := (naturalStateDerivative (ι := ι) g m).compLpL 2 (timeMeasure T)
    Tendsto (fun p => J (W p)) l (𝓝 (J W₀)) →
    Tendsto (fun p => D (W p)) l (𝓝 (D W₀)) → Tendsto W l (𝓝 W₀) := by
  intro J D hJ hD
  exact AddCircle.tendsto_timeL2_of_tensorHsInclusion_of_iteratedParameterDerivativeHs
    (ι := ι) (P := P) (l := l) g 1 m T W₀ W hJ hD

private theorem tendsto_projection_normalization
    {ι P : Type*} [Fintype ι] {l : Filter P}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) (T : ℝ)
    (V₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3))) T)
    (V : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3))) T) :
    let J := (stateProjection (ι := ι) g m).compLpL 2 (timeMeasure T)
    let A := (stateNormalization (ι := ι) g m).compLpL 2 (timeMeasure T)
    let N := (naturalStateProjection (ι := ι) g m).compLpL 2 (timeMeasure T)
    Tendsto (fun p => J (V p)) l (𝓝 (J V₀)) →
      Tendsto (fun p => N (A (V p))) l (𝓝 (N (A V₀))) := by
  intro J A N hJ
  have h := tendsto_compLpL (T := T) (P := P) (l := l)
    (projectionNormalization (ι := ι) g m) (J V₀) (fun p => J (V p)) hJ
  simpa only [J, A, N, projectionNormalization_compLpL] using h

private theorem tendsto_derivative_normalization
    {ι P : Type*} [Fintype ι] {l : Filter P}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) (T : ℝ)
    (V₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3))) T)
    (V : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3))) T) :
    let J := (stateDerivative (ι := ι) g m).compLpL 2 (timeMeasure T)
    let A := (stateNormalization (ι := ι) g m).compLpL 2 (timeMeasure T)
    let N := (naturalStateDerivative (ι := ι) g m).compLpL 2 (timeMeasure T)
    Tendsto (fun p => J (V p)) l (𝓝 (J V₀)) →
      Tendsto (fun p => N (A (V p))) l (𝓝 (N (A V₀))) := by
  intro J A N hJ
  have h := tendsto_compLpL (T := T) (P := P) (l := l)
    (derivativeNormalization (ι := ι) g) (J V₀) (fun p => J (V p)) hJ
  simpa only [J, A, N, derivativeNormalization_compLpL] using h

private theorem tendsto_iterated_graph
    {ι P : Type*} [Fintype ι] {l : Filter P}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ) (T : ℝ)
    (V₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3))) T)
    (V : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3))) T) :
    let J := (stateProjection (ι := ι) g m).compLpL 2 (timeMeasure T)
    let D := (stateDerivative (ι := ι) g m).compLpL 2 (timeMeasure T)
    Tendsto (fun p => J (V p)) l (𝓝 (J V₀)) →
    Tendsto (fun p => D (V p)) l (𝓝 (D V₀)) → Tendsto V l (𝓝 V₀) := by
  intro J D hJ hD
  let A := stateNormalization (ι := ι) g m
  let B := stateDenormalization (ι := ι) g m
  have hJForward := tendsto_projection_normalization (ι := ι) (P := P) (l := l)
    g m T V₀ V hJ
  have hDForward := tendsto_derivative_normalization (ι := ι) (P := P) (l := l)
    g m T V₀ V hD
  have hA := tendsto_normalized_graph
    (ι := ι) (P := P) (l := l) g m T
      (A.compLpL 2 (timeMeasure T) V₀)
      (fun p => A.compLpL 2 (timeMeasure T) (V p)) hJForward hDForward
  have hback := tendsto_compLpL (T := T) (P := P) (l := l)
    B (A.compLpL 2 (timeMeasure T) V₀)
    (fun p => A.compLpL 2 (timeMeasure T) (V p)) hA
  simpa only [A, B, stateDenormalization_compLpL] using hback

theorem tendsto_timeL2_duhamel_lifts_of_tendsto_forcing
    {ι P : Type*} [Fintype ι] {l : Filter P}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (m : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T)
    (F : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T)
    (FH₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 : ℝ))) T)
    (FH : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 : ℝ))) T)
    (V₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3))) T)
    (V : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 3))) T)
    (hlift₀ : iteratedParameterDerivativeDuhamelForcing g 0 m hT F₀ =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ 1))).compLpL
          2 (timeMeasure T) FH₀)
    (hlift : ∀ p, iteratedParameterDerivativeDuhamelForcing g 0 m hT (F p) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ 1))).compLpL
          2 (timeMeasure T) (FH p))
    (hV₀ : (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by linarith : (m : ℝ) + 2 ≤ (m : ℝ) + 3))).compLpL
          2 (timeMeasure T) V₀ = maximalRegularityDuhamelVectorField hT 0 F₀)
    (hV : ∀ p, (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by linarith : (m : ℝ) + 2 ≤ (m : ℝ) + 3))).compLpL
          2 (timeMeasure T) (V p) = maximalRegularityDuhamelVectorField hT 0 (F p))
    (hprojection : Tendsto (fun p => (ContinuousLinearMap.piLpMap 2
      (fun _ : ι => tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by linarith : (m : ℝ) + 2 ≤ (m : ℝ) + 3))).compLpL
          2 (timeMeasure T) (V p)) l
      (𝓝 ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by linarith : (m : ℝ) + 2 ≤ (m : ℝ) + 3))).compLpL
            2 (timeMeasure T) V₀)))
    (hFH : Tendsto FH l (𝓝 FH₀)) :
    Tendsto V l (𝓝 V₀) := by
  let D := (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) + 2 ≤ ((3 : ℕ) : ℝ))).comp
        ((AddCircle.iteratedParameterDerivativeHs g 3 m).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((3 + m : ℕ) : ℝ) ≤ (m : ℝ) + 3))))).compLpL
              2 (timeMeasure T)
  have hD₀ := iteratedParameterDerivativeHs_duhamel_field_of_lift
    (ι := ι) g m hT F₀ FH₀ V₀ hlift₀ hV₀
  have hD : ∀ p, D (V p) = maximalRegularityDuhamelVectorField hT 0 (FH p) :=
    fun p => iteratedParameterDerivativeHs_duhamel_field_of_lift
      (ι := ι) g m hT (F p) (FH p) (V p) (hlift p) (hV p)
  have hDF : Tendsto (fun p => D (V p)) l (𝓝 (D V₀)) := by
    have hbase := tendsto_duhamel_zero (ι := ι) (P := P) (l := l) g hT FH₀ FH hFH
    have hlimit : D V₀ = maximalRegularityDuhamelVectorField hT 0 FH₀ := hD₀
    exact hlimit.symm ▸ hbase.congr' (Eventually.of_forall fun p => (hD p).symm)
  exact tendsto_iterated_graph (ι := ι) (P := P) (l := l) g m T V₀ V hprojection hDF

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
