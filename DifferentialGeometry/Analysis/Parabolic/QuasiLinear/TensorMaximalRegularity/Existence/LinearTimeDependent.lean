import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.HeatEvolutionFinite
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.Inclusion
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Operator.L2

noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y Z W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  {T : ℝ}

private def timeResponse
    (L : X →L[ℝ] timeL2 Z T) (J : Z →L[ℝ] Y)
    (C : ℝ≥0) (hC : ∀ f, ∀ᵐ t ∂timeMeasure T, ‖J (L f t)‖ ≤ (C : ℝ) * ‖f‖)
    (A : ℝ → Y →L[ℝ] W) (hA : MemLp A 2 (timeMeasure T)) (f : X) : timeL2 W T :=
  timeOpL2 A hA (fun t => J (L f t))
    (J.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (L f)))
    (C * ‖f‖₊) (hC f)

omit [CompleteSpace W] in
private theorem timeResponse_ae
    (L : X →L[ℝ] timeL2 Z T) (J : Z →L[ℝ] Y)
    (C : ℝ≥0) (hC : ∀ f, ∀ᵐ t ∂timeMeasure T, ‖J (L f t)‖ ≤ (C : ℝ) * ‖f‖)
    (A : ℝ → Y →L[ℝ] W) (hA : MemLp A 2 (timeMeasure T)) (f : X) :
    timeResponse L J C hC A hA f =ᵐ[timeMeasure T] fun t => A t (J (L f t)) :=
  timeOpL2_apply_ae _ _ _ _ _ _

omit [CompleteSpace W] in
private theorem timeResponse_sub
    (L : X →L[ℝ] timeL2 Z T) (J : Z →L[ℝ] Y)
    (C : ℝ≥0) (hC : ∀ f, ∀ᵐ t ∂timeMeasure T, ‖J (L f t)‖ ≤ (C : ℝ) * ‖f‖)
    (A : ℝ → Y →L[ℝ] W) (hA : MemLp A 2 (timeMeasure T)) (f f' : X) :
    timeResponse L J C hC A hA f - timeResponse L J C hC A hA f' =
      timeResponse L J C hC A hA (f - f') := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (timeResponse L J C hC A hA f)
      (timeResponse L J C hC A hA f'),
    timeResponse_ae L J C hC A hA f,
    timeResponse_ae L J C hC A hA f',
    timeResponse_ae L J C hC A hA (f - f'),
    Lp.coeFn_sub (L f) (L f')] with t hout hf hf' hdiff hfield
  rw [hout, Pi.sub_apply, hf, hf', hdiff, map_sub L, hfield, Pi.sub_apply,
    map_sub J, map_sub]

omit [CompleteSpace W] in
private theorem timeResponse_norm_le
    (L : X →L[ℝ] timeL2 Z T) (J : Z →L[ℝ] Y)
    (C : ℝ≥0) (hC : ∀ f, ∀ᵐ t ∂timeMeasure T, ‖J (L f t)‖ ≤ (C : ℝ) * ‖f‖)
    (A : ℝ → Y →L[ℝ] W) (hA : MemLp A 2 (timeMeasure T)) (f : X) :
    ‖timeResponse L J C hC A hA f‖ ≤ (C : ℝ) * ‖hA.toLp A‖ * ‖f‖ := by
  apply (timeOpL2_norm_le A hA (fun t => J (L f t))
    (J.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (L f)))
    (C * ‖f‖₊) (hC f)).trans_eq
  simp only [NNReal.coe_mul, coe_nnnorm]
  ring

private theorem exists_fixed_timeResponse
    (L : timeL2 W T →L[ℝ] timeL2 Z T) (J : Z →L[ℝ] Y)
    (B C : ℝ≥0) (hL : ‖L‖ ≤ B)
    (hC : ∀ f, ∀ᵐ t ∂timeMeasure T, ‖J (L f t)‖ ≤ (C : ℝ) * ‖f‖)
    (A2 : ℝ → Z →L[ℝ] W) (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : ℝ≥0) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ C2)
    (A1 : ℝ → Y →L[ℝ] W) (hA1 : MemLp A1 2 (timeMeasure T))
    (f0 : timeL2 W T)
    (hsmall : (C2 : ℝ) * B + C * ‖hA1.toLp A1‖ < 1) :
    ∃! f : timeL2 W T,
      f = timeOp A2 hA2 C2 hC2 (L f) + timeResponse L J C hC A1 hA1 f + f0 := by
  let P := (timeOp A2 hA2 C2 hC2).comp L
  let R := timeResponse L J C hC A1 hA1
  have hP : ‖P‖ ≤ (C2 : ℝ) * B :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (timeOp_norm_le A2 hA2 C2 hC2) hL (norm_nonneg _) C2.coe_nonneg)
  have hR (f f' : timeL2 W T) :
      dist (R f) (R f') ≤ ((C : ℝ) * ‖hA1.toLp A1‖) * dist f f' := by
    simp only [R, dist_eq_norm, timeResponse_sub]
    exact timeResponse_norm_le L J C hC A1 hA1 (f - f')
  let K : ℝ≥0 := ⟨(C2 : ℝ) * B + C * ‖hA1.toLp A1‖, by positivity⟩
  let G : timeL2 W T → timeL2 W T := fun f => P f + R f + f0
  have hcontr : ContractingWith K G := by
    refine ⟨hsmall, LipschitzWith.of_dist_le_mul (fun f f' => ?_)⟩
    change dist (P f + R f + f0) (P f' + R f' + f0) ≤
      ((C2 : ℝ) * B + C * ‖hA1.toLp A1‖) * dist f f'
    rw [dist_add_right, add_mul]
    apply (dist_add_add_le _ _ _ _).trans
    exact add_le_add ((P.dist_le_opNorm f f').trans
      (mul_le_mul_of_nonneg_right hP dist_nonneg)) (hR f f')
  refine ⟨ContractingWith.fixedPoint G hcontr,
    (ContractingWith.fixedPoint_isFixedPt hcontr).symm, ?_⟩
  intro f hf
  exact hcontr.fixedPoint_unique hf.symm

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

private abbrev HsPi (a : ℝ) := PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)

theorem exists_unique_vector_forcing_of_l2_coefficients
    (hT : 0 < T)
    (A2 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : ℝ≥0) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ C2)
    (A1 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA1 : MemLp A1 2 (timeMeasure T))
    (f0 : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T)
    (hsmall : (C2 : ℝ) * (1 + T) + Real.sqrt (1 + T) * ‖hA1.toLp A1‖ < 1) :
    ∃! f : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T,
      ∀ᵐ t ∂timeMeasure T,
        f t = A2 t (maximalRegularityDuhamelVectorField hT 0 f t) +
          A1 t (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith))
              (maximalRegularityDuhamelVectorField hT 0 f t)) + f0 t := by
  let L := maximalRegularityVectorFieldL (ι := ι) (g := g) (r := r) (s := s) a hT.le
  let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (I := I) (M := M) (g := g) (r := r) (s := s)
    (show a + 1 ≤ a + 2 by linarith))
  let B : ℝ≥0 := ⟨1 + T, by linarith⟩
  let C : ℝ≥0 := ⟨Real.sqrt (1 + T), Real.sqrt_nonneg _⟩
  have hL : ‖L‖ ≤ B := maximalRegularityVectorFieldL_norm_le hT
  have hC (f) : ∀ᵐ t ∂timeMeasure T, ‖J (L f t)‖ ≤ (C : ℝ) * ‖f‖ := by
    dsimp only [L]
    rw [maximalRegularityVectorFieldL_eq_duhamel hT]
    exact maximalRegularityDuhamelVectorField_Ha1_ae_pointwise_le hT f
  obtain ⟨f, hf, huniq⟩ := exists_fixed_timeResponse L J B C hL hC A2 hA2 C2 hC2 A1 hA1 f0 hsmall
  refine ⟨f, ?_, ?_⟩
  · have hfield : L f = maximalRegularityDuhamelVectorField hT 0 f :=
      maximalRegularityVectorFieldL_eq_duhamel hT f
    filter_upwards [Lp.coeFn_add
        (timeOp A2 hA2 C2 hC2 (L f) + timeResponse L J C hC A1 hA1 f) f0,
      Lp.coeFn_add (timeOp A2 hA2 C2 hC2 (L f)) (timeResponse L J C hC A1 hA1 f),
      timeOp_apply_ae A2 hA2 C2 hC2 (L f),
      timeResponse_ae L J C hC A1 hA1 f] with t hout hadd h2 h1
    conv_lhs => rw [hf]
    rw [hout, Pi.add_apply, hadd, Pi.add_apply, h2, h1, hfield]
  · intro f' hf'
    apply huniq f'
    apply Lp.ext
    have hfield : L f' = maximalRegularityDuhamelVectorField hT 0 f' :=
      maximalRegularityVectorFieldL_eq_duhamel hT f'
    filter_upwards [hf', Lp.coeFn_add
        (timeOp A2 hA2 C2 hC2 (L f') + timeResponse L J C hC A1 hA1 f') f0,
      Lp.coeFn_add (timeOp A2 hA2 C2 hC2 (L f')) (timeResponse L J C hC A1 hA1 f'),
      timeOp_apply_ae A2 hA2 C2 hC2 (L f'),
      timeResponse_ae L J C hC A1 hA1 f'] with t ht hout hadd h2 h1
    rw [hout, Pi.add_apply, hadd, Pi.add_apply, h2, h1, hfield]
    exact ht

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal NNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity
variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

theorem memLp_affine_heatVectorField
    (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (A2 : ℝ → PiLp 2 (fun _ : ι => TensorHs g r s (a + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g r s a))
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : ℝ≥0) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ C2)
    (A1 : ℝ → PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g r s a))
    (hA1 : MemLp A1 2 (timeMeasure T))
    (f0 : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T) :
    MemLp (fun t => A2 t (heatVectorField a T u₀ t) +
      A1 t (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
          (heatVectorField a T u₀ t)) + f0 t) 2 (timeMeasure T) := by
  let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
  let w := heatVectorTrace hT.le hc u₀
  have hwc : ContinuousOn w (Icc (0 : ℝ) T) := heatVectorTrace_continuousOn hT.le hc u₀
  obtain ⟨t₁, ht₁, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (s := Icc (0 : ℝ) T) ⟨0, ⟨le_rfl, hT.le⟩⟩ hwc.norm
  have hbound : ∀ᵐ t ∂timeMeasure T, ‖J (heatVectorField a T u₀ t)‖ ≤ (‖w t₁‖₊ : ℝ) := by
    filter_upwards [heatVectorTrace_ae hT hc u₀, ae_restrict_mem measurableSet_Icc]
      with t ht hmem
    change w t = J (heatVectorField a T u₀ t) at ht
    rw [← ht]
    exact hmax hmem
  have h1 : MemLp (fun t => A1 t (J (heatVectorField a T u₀ t))) 2 (timeMeasure T) :=
    memLp_timeOpL2 A1 hA1 _
      (J.continuous.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable (heatVectorField a T u₀))) ‖w t₁‖₊ hbound
  exact ((memLp_timeOp A2 hA2 C2 hC2 (heatVectorField a T u₀)).add h1).add (Lp.memLp f0)


theorem exists_heat_vector_residual
    (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (A2 : ℝ → PiLp 2 (fun _ : ι => TensorHs g r s (a + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g r s a))
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : ℝ≥0) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ C2)
    (A1 : ℝ → PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g r s a))
    (hA1 : MemLp A1 2 (timeMeasure T))
    (f0 : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T) :
    ∃ F0 : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T,
      F0 =ᵐ[timeMeasure T] fun t => A2 t (heatVectorField a T u₀ t) +
        A1 t (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
            (heatVectorField a T u₀ t)) + f0 t := by
  have hmem := memLp_affine_heatVectorField hT hc u₀ A2 hA2 C2 hC2 A1 hA1 f0
  exact ⟨hmem.toLp _, hmem.coeFn_toLp⟩

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}


theorem exists_unique_heat_vector_forcing_of_l2_coefficients
    (hT : 0 < T)
    (u₀ : HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1))
    (A2 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : ℝ≥0) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ C2)
    (A1 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA1 : MemLp A1 2 (timeMeasure T))
    (f0 : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T)
    (hsmall : (C2 : ℝ) * (1 + T) + Real.sqrt (1 + T) * ‖hA1.toLp A1‖ < 1) :
    ∃! f : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T,
      ∀ᵐ t ∂timeMeasure T,
        f t = A2 t (heatDuhamelVectorField hT u₀ f t) +
          A1 t (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith))
              (heatDuhamelVectorField hT u₀ f t)) + f0 t := by
  let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (I := I) (M := M) (g := g) (r := r) (s := s)
    (show a + 1 ≤ a + 2 by linarith))
  let U := heatVectorField a T u₀
  have hc := DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator
    (I := I) (M := M) g r s
  obtain ⟨F0, hF0⟩ := exists_heat_vector_residual hT hc u₀ A2 hA2 C2 hC2 A1 hA1 f0
  have heq (f : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T) :
      (∀ᵐ t ∂timeMeasure T, f t = A2 t (heatDuhamelVectorField hT u₀ f t) +
        A1 t (J (heatDuhamelVectorField hT u₀ f t)) + f0 t) ↔
      (∀ᵐ t ∂timeMeasure T, f t = A2 t (maximalRegularityDuhamelVectorField hT 0 f t) +
        A1 t (J (maximalRegularityDuhamelVectorField hT 0 f t)) + F0 t) := by
    have hsum : (heatDuhamelVectorField hT u₀ f : ℝ → _) =ᵐ[timeMeasure T]
        fun t => U t + maximalRegularityDuhamelVectorField hT 0 f t := by
      rw [heatDuhamelVectorField_eq_add hT hc]
      exact Lp.coeFn_add _ _
    have hevent : ∀ᵐ t ∂timeMeasure T,
        A2 t (heatDuhamelVectorField hT u₀ f t) +
          A1 t (J (heatDuhamelVectorField hT u₀ f t)) + f0 t =
        A2 t (maximalRegularityDuhamelVectorField hT 0 f t) +
          A1 t (J (maximalRegularityDuhamelVectorField hT 0 f t)) + F0 t := by
      filter_upwards [hsum, hF0] with t hsumt hf0t
      rw [hsumt, hf0t, map_add, map_add, map_add]
      abel
    constructor
    · intro hf
      filter_upwards [hf, hevent] with t ht he
      exact ht.trans he
    · intro hf
      filter_upwards [hf, hevent] with t ht he
      exact ht.trans he.symm
  obtain ⟨f, hf, huniq⟩ := exists_unique_vector_forcing_of_l2_coefficients hT
    A2 hA2 C2 hC2 A1 hA1 F0 hsmall
  exact ⟨f, (heq f).mpr hf, fun f' hf' => huniq f' ((heq f').mp hf')⟩

theorem exists_heat_vector_evolution_of_l2_coefficients
    (hT : 0 < T)
    (u₀ : HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1))
    (A2 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : ℝ≥0) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ C2)
    (A1 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA1 : MemLp A1 2 (timeMeasure T))
    (f0 : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T)
    (hsmall : (C2 : ℝ) * (1 + T) + Real.sqrt (1 + T) * ‖hA1.toLp A1‖ < 1) :
    ∃ f : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T,
      (∀ᵐ t ∂timeMeasure T,
        (heatDuhamelVectorEvolution hT u₀ f).deriv t =
          ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
            (I := I) (M := M) (g := g) (r := r) (s := s) a)
              (heatDuhamelVectorField hT u₀ f t) +
          A2 t (heatDuhamelVectorField hT u₀ f t) +
          A1 t (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith))
              (heatDuhamelVectorField hT u₀ f t)) + f0 t) ∧
      timeH1.trace0 _ T (heatDuhamelVectorEvolution hT u₀ f) =
        ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 1 by linarith)) u₀ ∧
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith))).compLpL 2 (timeMeasure T)
          (heatDuhamelVectorField hT u₀ f) =
        (heatDuhamelVectorEvolution hT u₀ f).toFunL2 := by
  obtain ⟨f, hf, _⟩ := exists_unique_heat_vector_forcing_of_l2_coefficients hT
    u₀ A2 hA2 C2 hC2 A1 hA1 f0 hsmall
  have hc := DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator
    (I := I) (M := M) g r s
  refine ⟨f, ?_, heatDuhamelVectorEvolution_trace0 hT u₀ f,
    heatDuhamelVectorField_toFunL2 hT hc u₀ f⟩
  let Q := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
    (I := I) (M := M) (g := g) (r := r) (s := s) a)
  have hderiv := heatDuhamelVectorEvolution_timeDeriv hT hc u₀ f
  change (heatDuhamelVectorEvolution hT u₀ f).deriv =
    Q.compLpL 2 (timeMeasure T) (heatDuhamelVectorField hT u₀ f) + f at hderiv
  filter_upwards [hf,
    Lp.coeFn_add (Q.compLpL 2 (timeMeasure T) (heatDuhamelVectorField hT u₀ f)) f,
    Q.coeFn_compLpL (p := 2) (μ := timeMeasure T) (heatDuhamelVectorField hT u₀ f)]
    with t hft hadd hQ
  rw [hderiv, hadd, Pi.add_apply, hQ, hft]
  abel

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end
