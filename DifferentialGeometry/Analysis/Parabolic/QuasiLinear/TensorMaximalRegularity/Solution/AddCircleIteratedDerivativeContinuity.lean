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
