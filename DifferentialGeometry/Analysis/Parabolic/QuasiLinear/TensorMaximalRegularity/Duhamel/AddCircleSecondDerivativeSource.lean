import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleLinearizedBaseline
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff ENNReal

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem memLp_bilinear_of_continuousOn_right
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (B : X →L[ℝ] Y →L[ℝ] Z) {T : ℝ} {f : ℝ → X} {w : ℝ → Y}
    (hf : MemLp f 2 (timeMeasure T)) (hw : ContinuousOn w (Icc 0 T)) :
    MemLp (fun t => B (f t) (w t)) 2 (timeMeasure T) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  have hwm : AEStronglyMeasurable w (timeMeasure T) :=
    hw.aestronglyMeasurable measurableSet_Icc
  have hwb : ∀ᵐ t ∂timeMeasure T, ‖w t‖ ≤ C := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
    exact hC t ht
  exact B.memLp_of_bilin 2 hf (memLp_top_of_bound hwm C hwb)

def parameterSecondDerivativeSourceHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : TensorHs g 0 0 (((3 : ℕ) : ℝ) + 2))
    (a b : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))
    (v : TensorHs g 0 0 ((1 : ℕ) : ℝ)) : TensorHs g 0 0 ((1 : ℕ) : ℝ) :=
  let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
  let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
  let Q := parameterSecondDerivativeHs g 1
  let D := J.comp ((parameterDerivativeHs g 2).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)))
  let q₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((3 : ℕ) : ℝ))
      (parameterSecondDerivativeHs g 3 f₀)
  let m := scalarHsMul g 1 (by norm_num)
  m (Q a) v + (2 : ℝ) • m (D a) (D q₀) + m (K a) (Q q₀) + Q b

theorem memLp_parameterSecondDerivativeSourceHs_of_continuousOn
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : TensorHs g 0 0 (((3 : ℕ) : ℝ) + 2)) {T : ℝ}
    (a b : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) T)
    {v : ℝ → TensorHs g 0 0 ((1 : ℕ) : ℝ)} (hv : ContinuousOn v (Icc 0 T)) :
    MemLp (fun t => parameterSecondDerivativeSourceHs g f₀ (a t) (b t) (v t))
      2 (timeMeasure T) := by
  let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
  let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
  let Q := parameterSecondDerivativeHs g 1
  let D := J.comp ((parameterDerivativeHs g 2).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)))
  let q₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((3 : ℕ) : ℝ))
      (parameterSecondDerivativeHs g 3 f₀)
  let m := scalarHsMul g 1 (by norm_num)
  have h₁ := memLp_bilinear_of_continuousOn_right m
    ((Lp.memLp a).continuousLinearMap_comp Q) hv
  have h₂ := ((Lp.memLp a).continuousLinearMap_comp
    ((m.flip (D q₀)).comp D)).const_smul (2 : ℝ)
  have h₃ := (Lp.memLp a).continuousLinearMap_comp ((m.flip (Q q₀)).comp K)
  have h₄ := (Lp.memLp b).continuousLinearMap_comp Q
  exact ((h₁.add h₂).add h₃).add h₄

section

open Filter

theorem tensorHsInclusion_parameterSecondDerivativeSourceHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : TensorHs g 0 0 (((3 : ℕ) : ℝ) + 2))
    (a b : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))
    (v : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) + 2 ≤ ((3 : ℕ) : ℝ) + 2)
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let D := (parameterDerivativeHs g 1).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ)))
    let Q := (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))).comp
        ((parameterSecondDerivativeHs g 0).comp (tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))))
    let Q₂ := parameterSecondDerivativeHs g 2
    let m := scalarH0ContinuousMul g
    Z (parameterSecondDerivativeSourceHs g f₀ a b v) =
      m (C v) (Q (A a)) + m (C (J (A a))) (Q (Q₂ (P f₀))) +
        (2 : ℝ) • m (C (D (A a))) (Z (D (Q₂ (P f₀)))) + Q (A b) := by
  intro A P J Z C D Q Q₂ m
  let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
  let Dh := J.comp ((parameterDerivativeHs g 2).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)))
  let q₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((3 : ℕ) : ℝ))
      (parameterSecondDerivativeHs g 3 f₀)
  have hK (w : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) : K w = J (A w) :=
    tensorHsInclusion_trans_apply _ _ w
  have hD (w : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) : Dh w = D (A w) := by
    have h := parameterDerivativeHs_tensorHsInclusion g (by omega : 1 ≤ 2)
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2) w)
    simpa only [Dh, D, A, J, ContinuousLinearMap.comp_apply,
      ← tensorHsInclusion_trans_apply] using h.symm
  have hQ (w : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) :
      Z (parameterSecondDerivativeHs g 1 w) = Q (A w) := by
    have h := congrArg (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ)))
        (parameterSecondDerivativeHs_tensorHsInclusion g (by omega : 0 ≤ 1) w).symm
    simpa only [Z, Q, A, ContinuousLinearMap.comp_apply,
      ← tensorHsInclusion_trans_apply] using h
  have hbase : A q₀ = Q₂ (P f₀) := by
    have h := parameterSecondDerivativeHs_tensorHsInclusion g (by omega : 2 ≤ 3) f₀
    simpa only [A, q₀, Q₂, P, ← tensorHsInclusion_trans_apply] using h.symm
  change Z (scalarHsMul g 1 (by norm_num) (parameterSecondDerivativeHs g 1 a) v +
    (2 : ℝ) • scalarHsMul g 1 (by norm_num) (Dh a) (Dh q₀) +
      scalarHsMul g 1 (by norm_num) (K a) (parameterSecondDerivativeHs g 1 q₀) +
        parameterSecondDerivativeHs g 1 b) = _
  simp only [map_add, map_smul]
  rw [tensorHsInclusion_scalarHsMul_zero, tensorHsInclusion_scalarHsMul_zero,
    tensorHsInclusion_scalarHsMul_zero]
  rw [scalarH0ContinuousMul_scalarH1ToContinuous_comm g
    (parameterSecondDerivativeHs g 1 a) v]
  change m (C v) (Z (parameterSecondDerivativeHs g 1 a)) +
    (2 : ℝ) • m (C (Dh a)) (Z (Dh q₀)) +
      m (C (K a)) (Z (parameterSecondDerivativeHs g 1 q₀)) +
        Z (parameterSecondDerivativeHs g 1 b) = _
  simp only [hK, hD, hQ, hbase]
  abel

theorem tensorHsInclusion_parameterSecondDerivativeSourceHs_ae_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : TensorHs g 0 0 (((3 : ℕ) : ℝ) + 2)) {T : ℝ}
    (aHigh bHigh : ℝ → TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))
    (a b : ℝ → TensorHs g 0 0 ((2 : ℕ) : ℝ))
    (W : ℝ → TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))
    (U : ℝ → TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)) :
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) + 2 ≤ ((3 : ℕ) : ℝ) + 2)
    let B := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((3 : ℕ) : ℝ) + 2)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let D := (parameterDerivativeHs g 1).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ)))
    let Q := (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))).comp
        ((parameterSecondDerivativeHs g 0).comp (tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))))
    let Q₁ := parameterSecondDerivativeHs g 1
    let Q₂ := parameterSecondDerivativeHs g 2
    let m := scalarH0ContinuousMul g
    (fun t => A (aHigh t)) =ᵐ[timeMeasure T] a →
    (fun t => A (bHigh t)) =ᵐ[timeMeasure T] b →
    W =ᵐ[timeMeasure T] (fun t => K (U t)) →
    ∀ᵐ t ∂timeMeasure T,
      Z (parameterSecondDerivativeSourceHs g f₀ (aHigh t) (bHigh t)
        (Q₁ (B f₀ + W t))) =
      m (C (J (Q₂ (P f₀ + U t)))) (Q (a t)) +
        m (C (J (a t))) (Q (Q₂ (P f₀))) +
          (2 : ℝ) • m (C (D (a t))) (Z (D (Q₂ (P f₀)))) + Q (b t) := by
  intro A P B K J Z C D Q Q₁ Q₂ m ha hb hW
  filter_upwards [ha, hb, hW] with t hat hbt hWt
  have hbase : B f₀ = K (P f₀) := tensorHsInclusion_trans_apply _ _ f₀
  have hv : Q₁ (B f₀ + W t) = J (Q₂ (P f₀ + U t)) := by
    rw [hbase, hWt, ← K.map_add]
    exact parameterSecondDerivativeHs_tensorHsInclusion g (by omega : 1 ≤ 2) _
  have h := tensorHsInclusion_parameterSecondDerivativeSourceHs g f₀
    (aHigh t) (bHigh t) (Q₁ (B f₀ + W t))
  change Z (parameterSecondDerivativeSourceHs g f₀ (aHigh t) (bHigh t)
      (Q₁ (B f₀ + W t))) =
    m (C (Q₁ (B f₀ + W t))) (Q (A (aHigh t))) +
      m (C (J (A (aHigh t)))) (Q (Q₂ (P f₀))) +
        (2 : ℝ) • m (C (D (A (aHigh t)))) (Z (D (Q₂ (P f₀)))) +
          Q (A (bHigh t)) at h
  simpa only [hat, hbt, hv] using h

end

theorem memLp_parameterSecondDerivativeSourceHs_piLp_of_continuousOn
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((3 : ℕ) : ℝ) + 2))) {T : ℝ}
    (a : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) T)
    (b : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T)
    {v : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))}
    (hv : ContinuousOn v (Icc 0 T)) :
    MemLp (fun t => WithLp.toLp 2 (fun i =>
      parameterSecondDerivativeSourceHs g (f₀ i) (a t) (b t i) (v t i)))
        2 (timeMeasure T) := by
  apply MemLp.of_eval_piLp
  intro i
  have hbi : MemLp (fun t => b t i) 2 (timeMeasure T) := (Lp.memLp b).eval_piLp i
  have hvi : ContinuousOn (fun t => v t i) (Icc 0 T) :=
    (PiLp.continuous_apply 2 _ i).comp_continuousOn hv
  have hsource := memLp_parameterSecondDerivativeSourceHs_of_continuousOn
    g (f₀ i) a (hbi.toLp (fun t => b t i)) hvi
  apply hsource.ae_eq
  filter_upwards [hbi.coeFn_toLp] with t ht
  change parameterSecondDerivativeSourceHs g (f₀ i) (a t)
      ((hbi.toLp (fun t => b t i)) t) (v t i) =
    parameterSecondDerivativeSourceHs g (f₀ i) (a t) (b t i) (v t i)
  rw [ht]

def parameterSecondDerivativeSourceTimeL2
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((3 : ℕ) : ℝ) + 2))) {T : ℝ}
    (a : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) T)
    (b : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T)
    {v : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))}
    (hv : ContinuousOn v (Icc 0 T)) :
    timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T :=
  (memLp_parameterSecondDerivativeSourceHs_piLp_of_continuousOn g f₀ a b hv).toLp
    (fun t => WithLp.toLp 2 (fun i =>
      parameterSecondDerivativeSourceHs g (f₀ i) (a t) (b t i) (v t i)))

theorem parameterSecondDerivativeSourceTimeL2_coe
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((3 : ℕ) : ℝ) + 2))) {T : ℝ}
    (a : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) T)
    (b : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T)
    {v : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))}
    (hv : ContinuousOn v (Icc 0 T)) :
    ∀ᵐ t ∂timeMeasure T, ∀ i,
      parameterSecondDerivativeSourceTimeL2 g f₀ a b hv t i =
        parameterSecondDerivativeSourceHs g (f₀ i) (a t) (b t i) (v t i) := by
  have h := (memLp_parameterSecondDerivativeSourceHs_piLp_of_continuousOn
    g f₀ a b hv).coeFn_toLp
  filter_upwards [h] with t ht
  intro i
  exact congrArg (fun w => w i) ht

theorem tensorHsInclusion_parameterSecondDerivativeSourceTimeL2_ae_eq
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((3 : ℕ) : ℝ) + 2))) {T : ℝ}
    (aHigh : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) T)
    (bHigh : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T)
    {v : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))}
    (hv : ContinuousOn v (Icc 0 T))
    (a : ℝ → TensorHs g 0 0 ((2 : ℕ) : ℝ))
    (b : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((2 : ℕ) : ℝ)))
    (W : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (U : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2))) :
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) + 2 ≤ ((3 : ℕ) : ℝ) + 2)
    let B := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((3 : ℕ) : ℝ) + 2)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let D := (parameterDerivativeHs g 1).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ)))
    let Q := (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))).comp
        ((parameterSecondDerivativeHs g 0).comp (tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))))
    let Q₁ := parameterSecondDerivativeHs g 1
    let Q₂ := parameterSecondDerivativeHs g 2
    let m := scalarH0ContinuousMul g
    (fun t => A (aHigh t)) =ᵐ[timeMeasure T] a →
    (∀ᵐ t ∂timeMeasure T, ∀ i, A (bHigh t i) = b t i) →
    (∀ᵐ t ∂timeMeasure T, ∀ i, W t i = K (U t i)) →
    (∀ᵐ t ∂timeMeasure T, ∀ i, v t i = Q₁ (B (f₀ i) + W t i)) →
    ∀ᵐ t ∂timeMeasure T, ∀ i,
      Z (parameterSecondDerivativeSourceTimeL2 g f₀ aHigh bHigh hv t i) =
        m (C (J (Q₂ (P (f₀ i) + U t i)))) (Q (a t)) +
          m (C (J (a t))) (Q (Q₂ (P (f₀ i)))) +
            (2 : ℝ) • m (C (D (a t))) (Z (D (Q₂ (P (f₀ i))))) + Q (b t i) := by
  intro A P B K J Z C D Q Q₁ Q₂ m ha hb hW hV
  have hcoordinate : ∀ i, ∀ᵐ t ∂timeMeasure T,
      Z (parameterSecondDerivativeSourceHs g (f₀ i) (aHigh t) (bHigh t i)
        (Q₁ (B (f₀ i) + W t i))) =
        m (C (J (Q₂ (P (f₀ i) + U t i)))) (Q (a t)) +
          m (C (J (a t))) (Q (Q₂ (P (f₀ i)))) +
            (2 : ℝ) • m (C (D (a t))) (Z (D (Q₂ (P (f₀ i))))) + Q (b t i) := by
    intro i
    apply tensorHsInclusion_parameterSecondDerivativeSourceHs_ae_eq
      g (f₀ i) aHigh (fun t => bHigh t i) a (fun t => b t i)
        (fun t => W t i) (fun t => U t i) ha
    · filter_upwards [hb] with t ht
      exact ht i
    · filter_upwards [hW] with t ht
      exact ht i
  have hall : ∀ᵐ t ∂timeMeasure T, ∀ i,
      Z (parameterSecondDerivativeSourceHs g (f₀ i) (aHigh t) (bHigh t i)
        (Q₁ (B (f₀ i) + W t i))) =
        m (C (J (Q₂ (P (f₀ i) + U t i)))) (Q (a t)) +
          m (C (J (a t))) (Q (Q₂ (P (f₀ i)))) +
            (2 : ℝ) • m (C (D (a t))) (Z (D (Q₂ (P (f₀ i))))) + Q (b t i) :=
    ae_all_iff.mpr hcoordinate
  filter_upwards [parameterSecondDerivativeSourceTimeL2_coe g f₀ aHigh bHigh hv,
    hall, hV] with t ht hcompat hvt
  intro i
  rw [ht i, hvt i]
  exact hcompat i

end AddCircle
