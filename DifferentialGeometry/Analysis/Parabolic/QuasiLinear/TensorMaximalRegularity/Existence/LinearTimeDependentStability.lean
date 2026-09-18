import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import DifferentialGeometry.Analysis.FunctionalAnalysis.ContinuousLinearMap.Perturbation
import DifferentialGeometry.Analysis.FunctionalAnalysis.ContinuousLinearMap.ClosedRange
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.Inclusion
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.LinearTimeDependentContinuation
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Operator.Response

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

private abbrev HsPi (q : ℝ) := PiLp 2 (fun _ : ι => TensorHs g r s q)

private local instance vectorTensorHsNormedSpace (q : ℝ) :
    NormedSpace ℝ (PiLp 2 (fun _ : ι => TensorHs g r s q)) := inferInstance

private def heatForcingInclusion : HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
    HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))

private theorem heatForcingInclusion_field_bound (hT : 0 < T)
    (F : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T) :
    ∀ᵐ t ∂timeMeasure T,
      ‖heatForcingInclusion (maximalRegularityVectorFieldL a hT.le F t)‖ ≤
        Real.sqrt (1 + T) * ‖F‖ := by
  rw [maximalRegularityVectorFieldL_eq_duhamel hT]
  exact maximalRegularityDuhamelVectorField_Ha1_ae_pointwise_le hT F

def heatVectorForcingResidualL (hT : 0 < T)
    (A2 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : ℝ≥0) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ C2)
    (A1 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA1 : MemLp A1 2 (timeMeasure T)) :
    timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T →L[ℝ]
      timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T :=
  let L : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T →L[ℝ]
      timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2)) T :=
    maximalRegularityVectorFieldL a hT.le
  let J : HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) := heatForcingInclusion
  let C : ℝ≥0 := ⟨Real.sqrt (1 + T), Real.sqrt_nonneg _⟩
  have hC : ∀ F, ∀ᵐ t ∂timeMeasure T, ‖J (L F t)‖ ≤ (C : ℝ) * ‖F‖ := by
    intro F
    change ∀ᵐ t ∂timeMeasure T,
      ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
        (maximalRegularityVectorFieldL a hT.le F t)‖ ≤
        Real.sqrt (1 + T) * ‖F‖
    rw [maximalRegularityVectorFieldL_eq_duhamel hT]
    exact maximalRegularityDuhamelVectorField_Ha1_ae_pointwise_le hT F
  ContinuousLinearMap.id ℝ _ - (timeOp A2 hA2 C2 hC2).comp L -
    timeResponseL L J C hC A1 hA1

theorem heatVectorForcingResidualL_apply_ae (hT : 0 < T)
    (A2 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : ℝ≥0) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ C2)
    (A1 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA1 : MemLp A1 2 (timeMeasure T))
    (F : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T) :
    heatVectorForcingResidualL hT A2 hA2 C2 hC2 A1 hA1 F =ᵐ[timeMeasure T]
      fun t => F t - A2 t (maximalRegularityDuhamelVectorField hT 0 F t) -
        A1 t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith)))
          (maximalRegularityDuhamelVectorField hT 0 F t)) := by
  let L := maximalRegularityVectorFieldL (ι := ι) (g := g) (r := r) (s := s) a hT.le
  let C : ℝ≥0 := ⟨Real.sqrt (1 + T), Real.sqrt_nonneg _⟩
  let P := timeOp A2 hA2 C2 hC2 (L F)
  let D := timeResponseL L heatForcingInclusion C (heatForcingInclusion_field_bound (ι := ι) (g := g) (r := r) (s := s) (a := a) hT) A1 hA1 F
  change (F - P - D) =ᵐ[timeMeasure T] _
  have hfield : L F = maximalRegularityDuhamelVectorField hT 0 F :=
    maximalRegularityVectorFieldL_eq_duhamel hT F
  filter_upwards [Lp.coeFn_sub (F - P) D, Lp.coeFn_sub F P,
    timeOp_apply_ae A2 hA2 C2 hC2 (L F),
    timeResponseL_apply_ae L heatForcingInclusion C
      (heatForcingInclusion_field_bound (ι := ι) (g := g) (r := r) (s := s) (a := a) hT) A1 hA1 F] with t hout hsub hP hD
  rw [hout, Pi.sub_apply, hsub, Pi.sub_apply, hP, hD, hfield]
  rfl

theorem heatVectorForcingResidualL_eq_iff (hT : 0 < T)
    (A2 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : ℝ≥0) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ C2)
    (A1 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA1 : MemLp A1 2 (timeMeasure T))
    (F R : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T) :
    heatVectorForcingResidualL hT A2 hA2 C2 hC2 A1 hA1 F = R ↔
      ∀ᵐ t ∂timeMeasure T,
        F t = A2 t (maximalRegularityDuhamelVectorField hT 0 F t) +
          A1 t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith)))
            (maximalRegularityDuhamelVectorField hT 0 F t)) + R t := by
  have hres := heatVectorForcingResidualL_apply_ae hT A2 hA2 C2 hC2 A1 hA1 F
  constructor
  · intro h
    rw [h] at hres
    filter_upwards [hres] with t ht
    have heq := sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp ht.symm)
    rw [heq]
    abel
  · intro h
    apply Lp.ext
    filter_upwards [hres, h] with t ht hFt
    rw [ht, hFt]
    abel

theorem heatVectorForcingResidualL_eq_iff_heat (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (A2 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : ℝ≥0) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ C2)
    (A1 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA1 : MemLp A1 2 (timeMeasure T))
    (F R : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T) :
    heatVectorForcingResidualL hT A2 hA2 C2 hC2 A1 hA1 F = R ↔
      ∀ᵐ t ∂timeMeasure T,
        F t = A2 t (heatDuhamelVectorField hT 0 F t) +
          A1 t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith)))
            (heatDuhamelVectorField hT 0 F t)) + R t := by
  have hfield : heatDuhamelVectorField hT 0 F =
      maximalRegularityDuhamelVectorField hT 0 F := by
    simpa only [map_zero] using heatDuhamelVectorField_inclusion hT hc 0 F
  rw [hfield]
  exact heatVectorForcingResidualL_eq_iff hT A2 hA2 C2 hC2 A1 hA1 F R

variable {b : ℝ}

theorem heatVectorForcingResidualL_comp_tensorHsInclusion
    (hab : a ≤ b) (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (A2h : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (b + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) b)
    (hA2h : AEStronglyMeasurable A2h (timeMeasure T))
    (C2h : ℝ≥0) (hC2h : ∀ᵐ t ∂timeMeasure T, ‖A2h t‖ ≤ C2h)
    (A1h : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (b + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) b)
    (hA1h : MemLp A1h 2 (timeMeasure T))
    (A2l : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA2l : AEStronglyMeasurable A2l (timeMeasure T))
    (C2l : ℝ≥0) (hC2l : ∀ᵐ t ∂timeMeasure T, ‖A2l t‖ ≤ C2l)
    (A1l : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA1l : MemLp A1l 2 (timeMeasure T))
    (hA2 : ∀ᵐ t ∂timeMeasure T, ∀ x,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)) (A2h t x) =
        A2l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 2 ≤ b + 2 by linarith))) x))
    (hA1 : ∀ᵐ t ∂timeMeasure T, ∀ x,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)) (A1h t x) =
        A1l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))) x)) :
    let J0L := (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T)
    (heatVectorForcingResidualL hT A2l hA2l C2l hC2l A1l hA1l).comp J0L =
      J0L.comp (heatVectorForcingResidualL hT A2h hA2h C2h hC2h A1h hA1h) := by
  let J0 : HsPi (ι := ι) (g := g) (r := r) (s := s) b →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) hab)
  let J1 : HsPi (ι := ι) (g := g) (r := r) (s := s) (b + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))
  let J2 : HsPi (ι := ι) (g := g) (r := r) (s := s) (b + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 2 ≤ b + 2 by linarith))
  let Kh : HsPi (ι := ι) (g := g) (r := r) (s := s) (b + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) (b + 1) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show b + 1 ≤ b + 2 by linarith))
  let Kl : HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
  let J0L := J0.compLpL 2 (timeMeasure T)
  let Qh := heatVectorForcingResidualL hT A2h hA2h C2h hC2h A1h hA1h
  let Ql := heatVectorForcingResidualL hT A2l hA2l C2l hC2l A1l hA1l
  change Ql.comp J0L = J0L.comp Qh
  apply ContinuousLinearMap.ext
  intro FH
  change Ql (J0L FH) = J0L (Qh FH)
  let DH := maximalRegularityDuhamelVectorField hT 0 FH
  let DL := maximalRegularityDuhamelVectorField hT 0 (J0L FH)
  have hfield : J2.compLpL 2 (timeMeasure T) DH = DL := by
    dsimp only [DH, DL, J0L, J0, J2]
    simpa only [map_zero] using
      maximalRegularityDuhamelVectorField_compLpL_tensorHsInclusion hab hT hc 0 FH
  have hfieldAE : ∀ᵐ t ∂timeMeasure T, J2 (DH t) = DL t := by
    have h := J2.coeFn_compLpL (p := 2) (μ := timeMeasure T) DH
    rw [hfield] at h
    exact h.symm
  have hJK (x : HsPi (ι := ι) (g := g) (r := r) (s := s) (b + 2)) :
      J1 (Kh x) = Kl (J2 x) := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hlow := heatVectorForcingResidualL_apply_ae hT A2l hA2l C2l hC2l A1l hA1l
    (J0L FH)
  have hhigh := heatVectorForcingResidualL_apply_ae hT A2h hA2h C2h hC2h A1h hA1h FH
  apply Lp.ext
  filter_upwards [hlow, hhigh, hfieldAE,
    J0.coeFn_compLpL (p := 2) (μ := timeMeasure T) FH,
    J0.coeFn_compLpL (p := 2) (μ := timeMeasure T) (Qh FH), hA2, hA1]
    with t hl hh hd hF hQ ha2 ha1
  change Ql (J0L FH) t = (J0L FH) t - A2l t (DL t) - A1l t (Kl (DL t)) at hl
  change Qh FH t = FH t - A2h t (DH t) - A1h t (Kh (DH t)) at hh
  rw [hl, hQ, hh, map_sub, map_sub, hF]
  have ha2' : J0 (A2h t (DH t)) = A2l t (J2 (DH t)) := ha2 _
  have ha1' : J0 (A1h t (Kh (DH t))) = A1l t (J1 (Kh (DH t))) := ha1 _
  rw [ha2', ha1', hJK, hd]

theorem exists_heat_vector_forcing_norm_le_of_tensorHsInclusion
    (hab : a ≤ b) (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (A2h : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (b + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) b)
    (hA2h : AEStronglyMeasurable A2h (timeMeasure T))
    (C2h : ℝ≥0) (hC2h : ∀ᵐ t ∂timeMeasure T, ‖A2h t‖ ≤ C2h)
    (A1h : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (b + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) b)
    (hA1h : MemLp A1h 2 (timeMeasure T))
    (A2l : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA2l : AEStronglyMeasurable A2l (timeMeasure T))
    (C2l : ℝ≥0) (hC2l : ∀ᵐ t ∂timeMeasure T, ‖A2l t‖ ≤ C2l)
    (A1l : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA1l : MemLp A1l 2 (timeMeasure T))
    (hA2 : ∀ᵐ t ∂timeMeasure T, ∀ x,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)) (A2h t x) =
        A2l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 2 ≤ b + 2 by linarith))) x))
    (hA1 : ∀ᵐ t ∂timeMeasure T, ∀ x,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)) (A1h t x) =
        A1l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))) x))
    (hC2h_lt : (C2h : ℝ) < 1) (hC2l_lt : (C2l : ℝ) < 1) :
    ∃ C ≥ (0 : ℝ), ∀ F : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) b) T,
      ‖F‖ ≤ C * max
        ‖(ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T) F‖
        ‖heatVectorForcingResidualL hT A2h hA2h C2h hC2h A1h hA1h F‖ := by
  let J₀ : HsPi (ι := ι) (g := g) (r := r) (s := s) b →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) hab)
  let J := J₀.compLpL 2 (timeMeasure T)
  let QH := heatVectorForcingResidualL hT A2h hA2h C2h hC2h A1h hA1h
  let QL := heatVectorForcingResidualL hT A2l hA2l C2l hC2l A1l hA1l
  have hJ₀ : Function.Injective J₀ := by
    intro x y hxy
    apply PiLp.ext
    intro i
    apply tensorHsInclusion_injective hab
    exact congrArg (fun v => v i) hxy
  have hJ : Function.Injective J := by
    intro F G hFG
    apply Lp.ext
    have hF := J₀.coeFn_compLpL (p := 2) (μ := timeMeasure T) F
    have hG := J₀.coeFn_compLpL (p := 2) (μ := timeMeasure T) G
    change J F =ᵐ[timeMeasure T] fun t => J₀ (F t) at hF
    rw [hFG] at hF
    filter_upwards [hF, hG] with t hFt hGt
    exact hJ₀ (hFt.symm.trans hGt)
  have hcomm : QL.comp J = J.comp QH :=
    heatVectorForcingResidualL_comp_tensorHsInclusion hab hT hc
      A2h hA2h C2h hC2h A1h hA1h A2l hA2l C2l hC2l A1l hA1l hA2 hA1
  have hlift (FL : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T)
      (RH : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) b) T)
      (hR : QL FL = J RH) : ∃ FH, J FH = FL ∧ QH FH = RH := by
    have hlow := (heatVectorForcingResidualL_eq_iff_heat
      hT hc A2l hA2l C2l hC2l A1l hA1l FL (J RH)).mp hR
    obtain ⟨FH, hFH, _⟩ := exists_unique_heat_vector_forcing_lift_of_principal_norm_lt_one
      hab hT hc 0 FL A2h hA2h C2h hC2h A1h hA1h RH
      A2l hA2l C2l hC2l A1l hA1l (J RH) hA2 hA1 rfl hlow
      hC2h_lt hC2l_lt 0 (by rw [map_zero])
    exact ⟨FH, hFH.2.symm, (heatVectorForcingResidualL_eq_iff_heat
      hT hc A2h hA2h C2h hC2h A1h hA1h FH RH).mpr hFH.1⟩
  exact ContinuousLinearMap.exists_norm_le_max_of_lifting J QH QL J hJ hcomm hlift

private theorem norm_neg_comp_sub_le
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (P : Y →L[ℝ] Z) (L : X →L[ℝ] Y) (R : X →L[ℝ] Z)
    {D B C : ℝ} (hD : 0 ≤ D) (hP : ‖P‖ ≤ D) (hL : ‖L‖ ≤ B) (hR : ‖R‖ ≤ C) :
    ‖-(P.comp L) - R‖ ≤ D * B + C := by
  have hn : ‖-(P.comp L) - R‖ ≤ ‖P.comp L‖ + ‖R‖ := by
    simpa only [norm_neg] using norm_sub_le (-(P.comp L)) R
  exact hn.trans (add_le_add
    ((ContinuousLinearMap.opNorm_comp_le P L).trans
      (mul_le_mul hP hL (norm_nonneg L) hD)) hR)

theorem heatVectorForcingResidualL_sub_norm_le (hT : 0 < T)
    (A2 B2 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (hB2 : AEStronglyMeasurable B2 (timeMeasure T))
    (CA CB D : ℝ≥0)
    (hCA : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ CA)
    (hCB : ∀ᵐ t ∂timeMeasure T, ‖B2 t‖ ≤ CB)
    (hD : ∀ᵐ t ∂timeMeasure T, ‖A2 t - B2 t‖ ≤ D)
    (A1 B1 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA1 : MemLp A1 2 (timeMeasure T)) (hB1 : MemLp B1 2 (timeMeasure T)) :
    ‖heatVectorForcingResidualL hT A2 hA2 CA hCA A1 hA1 -
      heatVectorForcingResidualL hT B2 hB2 CB hCB B1 hB1‖ ≤
        (D : ℝ) * (1 + T) +
          Real.sqrt (1 + T) * ‖hA1.toLp A1 - hB1.toLp B1‖ := by
  let L := maximalRegularityVectorFieldL (ι := ι) (g := g) (r := r) (s := s) a hT.le
  let J : HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
  let C : ℝ≥0 := ⟨Real.sqrt (1 + T), Real.sqrt_nonneg _⟩
  have hC : ∀ F, ∀ᵐ t ∂timeMeasure T, ‖J (L F t)‖ ≤ (C : ℝ) * ‖F‖ := by
    intro F
    change ∀ᵐ t ∂timeMeasure T,
      ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
        (maximalRegularityVectorFieldL a hT.le F t)‖ ≤
        Real.sqrt (1 + T) * ‖F‖
    rw [maximalRegularityVectorFieldL_eq_duhamel hT]
    exact maximalRegularityDuhamelVectorField_Ha1_ae_pointwise_le hT F
  let PA := timeOp A2 hA2 CA hCA
  let PB := timeOp B2 hB2 CB hCB
  let RA := timeResponseL L J C hC A1 hA1
  let RB := timeResponseL L J C hC B1 hB1
  have hresp : ‖RA - RB‖ ≤
      Real.sqrt (1 + T) * ‖hA1.toLp A1 - hB1.toLp B1‖ :=
    timeResponseL_sub_norm_le L J C hC A1 B1 hA1 hB1
  have hprincipal : ‖PA - PB‖ ≤ (D : ℝ) :=
    timeOp_sub_norm_le A2 B2 hA2 hB2 CA CB D hCA hCB hD
  have hL : ‖L‖ ≤ 1 + T := maximalRegularityVectorFieldL_norm_le hT
  have hres : heatVectorForcingResidualL hT A2 hA2 CA hCA A1 hA1 -
      heatVectorForcingResidualL hT B2 hB2 CB hCB B1 hB1 =
        -((PA - PB).comp L) - (RA - RB) := by
    dsimp only [heatVectorForcingResidualL]
    change (ContinuousLinearMap.id ℝ _ - PA.comp L - RA) -
      (ContinuousLinearMap.id ℝ _ - PB.comp L - RB) = _
    rw [ContinuousLinearMap.sub_comp]
    abel
  rw [hres]
  exact norm_neg_comp_sub_le (PA - PB) L (RA - RB) D.coe_nonneg hprincipal hL hresp

open Filter in
open scoped Topology in
theorem tendsto_heatVectorForcingResidualL
    {P : Type*} {l : Filter P} (hT : 0 < T)
    (A2 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (CA : ℝ≥0) (hCA : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ CA)
    (A1 : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA1 : MemLp A1 2 (timeMeasure T))
    (B2 : P → ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hB2 : ∀ p, AEStronglyMeasurable (B2 p) (timeMeasure T))
    (CB D : P → ℝ≥0)
    (hCB : ∀ p, ∀ᵐ t ∂timeMeasure T, ‖B2 p t‖ ≤ CB p)
    (hD : ∀ᶠ p in l, ∀ᵐ t ∂timeMeasure T, ‖B2 p t - A2 t‖ ≤ D p)
    (hDlim : Tendsto (fun p => (D p : ℝ)) l (𝓝 0))
    (B1 : P → ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hB1 : ∀ p, MemLp (B1 p) 2 (timeMeasure T))
    (hB1lim : Tendsto (fun p => (hB1 p).toLp (B1 p)) l (𝓝 (hA1.toLp A1))) :
    Tendsto (fun p => heatVectorForcingResidualL hT (B2 p) (hB2 p) (CB p)
      (hCB p) (B1 p) (hB1 p)) l
      (𝓝 (heatVectorForcingResidualL hT A2 hA2 CA hCA A1 hA1)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hBnorm := tendsto_iff_norm_sub_tendsto_zero.mp hB1lim
  have hbound := (hDlim.mul_const (1 + T)).add
    (hBnorm.const_mul (Real.sqrt (1 + T)))
  have hzero : Tendsto (fun p => (D p : ℝ) * (1 + T) +
      Real.sqrt (1 + T) * ‖(hB1 p).toLp (B1 p) - hA1.toLp A1‖) l (𝓝 0) := by
    simpa only [zero_mul, mul_zero, add_zero] using hbound
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hD.mono fun p hp => heatVectorForcingResidualL_sub_norm_le hT
      (B2 p) A2 (hB2 p) hA2 (CB p) CA (D p) (hCB p) hCA hp
      (B1 p) A1 (hB1 p) hA1) hzero

open scoped Topology in
open Filter in
theorem tendsto_heat_vector_forcing_of_tendsto_residual
    {P : Type*} {l : Filter P} (hab : a ≤ b) (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (A2h : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (b + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) b)
    (hA2h : AEStronglyMeasurable A2h (timeMeasure T))
    (C2h : ℝ≥0) (hC2h : ∀ᵐ t ∂timeMeasure T, ‖A2h t‖ ≤ C2h)
    (A1h : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (b + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) b)
    (hA1h : MemLp A1h 2 (timeMeasure T))
    (A2l : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA2l : AEStronglyMeasurable A2l (timeMeasure T))
    (C2l : ℝ≥0) (hC2l : ∀ᵐ t ∂timeMeasure T, ‖A2l t‖ ≤ C2l)
    (A1l : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA1l : MemLp A1l 2 (timeMeasure T))
    (hA2 : ∀ᵐ t ∂timeMeasure T, ∀ x,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)) (A2h t x) =
        A2l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 2 ≤ b + 2 by linarith))) x))
    (hA1 : ∀ᵐ t ∂timeMeasure T, ∀ x,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)) (A1h t x) =
        A1l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))) x))
    (hC2h_lt : (C2h : ℝ) < 1) (hC2l_lt : (C2l : ℝ) < 1)
    (A2p : P → ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (b + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) b)
    (hA2p : ∀ p, AEStronglyMeasurable (A2p p) (timeMeasure T))
    (C2p : P → ℝ≥0) (hC2p : ∀ p, ∀ᵐ t ∂timeMeasure T, ‖A2p p t‖ ≤ C2p p)
    (A1p : P → ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (b + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) b)
    (hA1p : ∀ p, MemLp (A1p p) 2 (timeMeasure T))
    (F₀ : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) b) T)
    (F : P → timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) b) T)
    (hQ : Tendsto
      (fun p => heatVectorForcingResidualL hT (A2p p) (hA2p p) (C2p p) (hC2p p)
        (A1p p) (hA1p p)) l
      (𝓝 (heatVectorForcingResidualL hT A2h hA2h C2h hC2h A1h hA1h)))
    (hF : Tendsto
      (fun p => (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T) (F p)) l
      (𝓝 ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T) F₀)))
    (hsource : Tendsto
      (fun p => heatVectorForcingResidualL hT (A2p p) (hA2p p) (C2p p) (hC2p p)
        (A1p p) (hA1p p) (F p)) l
      (𝓝 (heatVectorForcingResidualL hT A2h hA2h C2h hC2h A1h hA1h F₀))) :
    Tendsto F l (𝓝 F₀) := by
  obtain ⟨C, hC, hbound⟩ := exists_heat_vector_forcing_norm_le_of_tensorHsInclusion
    hab hT hc A2h hA2h C2h hC2h A1h hA1h
    A2l hA2l C2l hC2l A1l hA1l hA2 hA1 hC2h_lt hC2l_lt
  exact ContinuousLinearMap.tendsto_of_tendsto_apply_of_norm_le_max
    ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T))
    (heatVectorForcingResidualL hT A2h hA2h C2h hC2h A1h hA1h)
    (fun p => heatVectorForcingResidualL hT (A2p p) (hA2p p) (C2p p) (hC2p p)
      (A1p p) (hA1p p)) F₀ F hC hbound hQ hF hsource

theorem heatVectorForcingResidualL_eq_iff_tensorHsInclusion
    (hab : a ≤ b) (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (A2h : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (b + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) b)
    (hA2h : AEStronglyMeasurable A2h (timeMeasure T))
    (C2h : ℝ≥0) (hC2h : ∀ᵐ t ∂timeMeasure T, ‖A2h t‖ ≤ C2h)
    (A1h : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (b + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) b)
    (hA1h : MemLp A1h 2 (timeMeasure T))
    (A2l : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 2) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA2l : AEStronglyMeasurable A2l (timeMeasure T))
    (C2l : ℝ≥0) (hC2l : ∀ᵐ t ∂timeMeasure T, ‖A2l t‖ ≤ C2l)
    (A1l : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1) →L[ℝ]
      HsPi (ι := ι) (g := g) (r := r) (s := s) a)
    (hA1l : MemLp A1l 2 (timeMeasure T))
    (hA2 : ∀ᵐ t ∂timeMeasure T, ∀ x,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)) (A2h t x) =
        A2l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 2 ≤ b + 2 by linarith))) x))
    (hA1 : ∀ᵐ t ∂timeMeasure T, ∀ x,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)) (A1h t x) =
        A1l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))) x))
    (FH R : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) b) T) :
    let J := (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T)
    heatVectorForcingResidualL hT A2h hA2h C2h hC2h A1h hA1h FH = R ↔
      heatVectorForcingResidualL hT A2l hA2l C2l hC2l A1l hA1l (J FH) = J R := by
  let J₀ := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) hab)
  intro J
  have hJ₀ : Function.Injective J₀ := by
    intro x y hxy
    apply PiLp.ext
    intro i
    exact tensorHsInclusion_injective hab (congrArg (fun v => v i) hxy)
  have hJ : Function.Injective J := by
    intro x y hxy
    apply Lp.ext
    have hx := J₀.coeFn_compLpL (p := 2) (μ := timeMeasure T) x
    have hy := J₀.coeFn_compLpL (p := 2) (μ := timeMeasure T) y
    change J x =ᵐ[timeMeasure T] fun t => J₀ (x t) at hx
    rw [hxy] at hx
    filter_upwards [hx, hy] with t ht ht'
    exact hJ₀ (ht.symm.trans ht')
  have hcomm := DFunLike.congr_fun
    (heatVectorForcingResidualL_comp_tensorHsInclusion hab hT hc
      A2h hA2h C2h hC2h A1h hA1h A2l hA2l C2l hC2l A1l hA1l hA2 hA1) FH
  change heatVectorForcingResidualL hT A2l hA2l C2l hC2l A1l hA1l (J FH) =
    J (heatVectorForcingResidualL hT A2h hA2h C2h hC2h A1h hA1h FH) at hcomm
  rw [hcomm]
  exact ⟨congrArg J, fun h => hJ h⟩


end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end

noncomputable section

open Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

private theorem ae_norm_le_lpTop_norm
    {Ω Y : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [NormedAddCommGroup Y]
    (f : Lp Y ∞ μ) : ∀ᵐ t ∂μ, ‖f t‖ ≤ ‖f‖ := by
  simpa only [← toReal_eLpNorm (Lp.memLp f).aestronglyMeasurable, Lp.norm_def] using
    ae_le_lpNorm_exponent_top (Lp.memLp f)

theorem tendsto_heatVectorForcingResidualL_of_tendsto_lp
    {P : Type*} {l : Filter P} (hT : 0 < T)
    (A2 : ℝ → PiLp 2 (fun _ : ι => TensorHs g r s (a + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g r s a))
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (CA : ℝ≥0) (hCA : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ CA)
    (A1 : ℝ → PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g r s a))
    (hA1 : MemLp A1 2 (timeMeasure T))
    (B2 : P → ℝ → PiLp 2 (fun _ : ι => TensorHs g r s (a + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g r s a))
    (hB2 : ∀ p, AEStronglyMeasurable (B2 p) (timeMeasure T))
    (CB : P → ℝ≥0)
    (hCB : ∀ p, ∀ᵐ t ∂timeMeasure T, ‖B2 p t‖ ≤ CB p)
    (B1 : P → ℝ → PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g r s a))
    (hB1 : ∀ p, MemLp (B1 p) 2 (timeMeasure T))
    (Q : P → Lp ((PiLp 2 (fun _ : ι => TensorHs g r s (a + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g r s a)) ∞ (timeMeasure T))
    (Q0 : Lp ((PiLp 2 (fun _ : ι => TensorHs g r s (a + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g r s a)) ∞ (timeMeasure T))
    (hQ : ∀ p, Q p =ᵐ[timeMeasure T] B2 p)
    (hQ0 : Q0 =ᵐ[timeMeasure T] A2)
    (hQlim : Tendsto Q l (𝓝 Q0))
    (hB1lim : Tendsto (fun p => (hB1 p).toLp (B1 p)) l (𝓝 (hA1.toLp A1))) :
    Tendsto (fun p => heatVectorForcingResidualL hT (B2 p) (hB2 p) (CB p)
      (hCB p) (B1 p) (hB1 p)) l
      (𝓝 (heatVectorForcingResidualL hT A2 hA2 CA hCA A1 hA1)) := by
  let D : P → ℝ≥0 := fun p => ‖Q p - Q0‖₊
  apply tendsto_heatVectorForcingResidualL hT A2 hA2 CA hCA A1 hA1
    B2 hB2 CB D hCB _ _ B1 hB1 hB1lim
  · apply Eventually.of_forall
    intro p
    filter_upwards [hQ p, hQ0, Lp.coeFn_sub (Q p) Q0,
      ae_norm_le_lpTop_norm (Q p - Q0)] with t ht ht0 hsub hbound
    rw [hsub] at hbound
    simpa only [Pi.sub_apply, ht, ht0, D, coe_nnnorm] using hbound
  · exact tendsto_iff_norm_sub_tendsto_zero.mp hQlim

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
