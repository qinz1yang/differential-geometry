import DifferentialGeometry.Analysis.Spectral.Scalar.Eigenfunction
import DifferentialGeometry.Analysis.Spectral.Scalar.WeylBounds
import DifferentialGeometry.Analysis.Spectral.HeatTrace
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.HeatEquation

open MeasureTheory
open Spectral
open Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def heatKernel (g : SmoothRiemannianMetric I M) (t : Real) (x y : M) : Real :=
  ∑' i : TensorEigenIdx (I := I) (M := M) g 0 0,
    Real.exp (-TensorEigenIdx.lambda i * t) * (scalarEigenFunction g i).toFun x *
      (scalarEigenFunction g i).toFun y

theorem exists_summable_heatKernel_majorant (g : SmoothRiemannianMetric I M) {a : Real} (ha : 0 < a) :
    ∃ b : TensorEigenIdx (I := I) (M := M) g 0 0 → Real, Summable b ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 0) (t : Real), a ≤ t → ∀ x y : M,
        |Real.exp (-TensorEigenIdx.lambda i * t) * (scalarEigenFunction g i).toFun x *
          (scalarEigenFunction g i).toFun y| ≤ b i := by
  obtain ⟨C, hC, hb⟩ := scalarEigenFunction_abs_le g
  let q : Real := (Module.finrank Real E / 2 + 1 : Nat)
  have hsum := summable_weighted_heat_trace (scalar_eigen_tail g) q
    (by dsimp [q]; positivity) (half_pos ha)
  have hsum' : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 0 =>
      tensorSobolevWeight i q * Real.exp (-TensorEigenIdx.lambda i * a)) := by
    apply hsum.congr
    intro i
    congr 1
    congr 1
    ring
  refine ⟨fun i => C ^ 2 * (tensorSobolevWeight i q *
    Real.exp (-TensorEigenIdx.lambda i * a)), hsum'.mul_left (C ^ 2), ?_⟩
  intro i t hat x y
  let R := (1 + TensorEigenIdx.lambda i) ^ (q / 2)
  have hbase : 0 ≤ 1 + TensorEigenIdx.lambda i := by
    linarith [tensor_lambda_nonneg (I := I) (M := M) i]
  have hR : 0 ≤ R := Real.rpow_nonneg hbase _
  have hprod : |(scalarEigenFunction g i).toFun x| * |(scalarEigenFunction g i).toFun y| ≤
      (C * R) * (C * R) :=
    mul_le_mul (hb i x) (hb i y) (abs_nonneg _) (mul_nonneg hC hR)
  have hpow : R * R = tensorSobolevWeight i q := by
    rw [← pow_two]
    dsimp [R, tensorSobolevWeight]
    rw [← Real.rpow_two, ← Real.rpow_mul hbase]
    congr 1
    ring
  have hexp : Real.exp (-TensorEigenIdx.lambda i * t) ≤
      Real.exp (-TensorEigenIdx.lambda i * a) := by
    apply Real.exp_le_exp.mpr
    nlinarith [tensor_lambda_nonneg (I := I) (M := M) i]
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ = Real.exp (-TensorEigenIdx.lambda i * t) *
        (|(scalarEigenFunction g i).toFun x| * |(scalarEigenFunction g i).toFun y|) := by ring
    _ ≤ Real.exp (-TensorEigenIdx.lambda i * a) * ((C * R) * (C * R)) :=
      mul_le_mul hexp hprod (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le
    _ = _ := by
      rw [show (C * R) * (C * R) = C ^ 2 * (R * R) by ring, hpow]
      ring

theorem heatKernel_summable (g : SmoothRiemannianMetric I M) {t : Real} (ht : 0 < t)
    (x y : M) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 0 =>
      Real.exp (-TensorEigenIdx.lambda i * t) * (scalarEigenFunction g i).toFun x *
        (scalarEigenFunction g i).toFun y) := by
  obtain ⟨b, hb, hbound⟩ := exists_summable_heatKernel_majorant g ht
  exact Summable.of_norm_bounded hb (fun i => hbound i t le_rfl x y)

theorem heatKernel_symm (g : SmoothRiemannianMetric I M) (t : Real) (x y : M) :
    heatKernel g t x y = heatKernel g t y x := by
  apply tsum_congr
  intro i
  ring

theorem continuousOn_heatKernel (g : SmoothRiemannianMetric I M) :
    ContinuousOn (fun q : Real × (M × M) => heatKernel g q.1 q.2.1 q.2.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  intro q hq
  have ha : 0 < q.1 / 2 := half_pos hq.1
  obtain ⟨b, hb, hbound⟩ := exists_summable_heatKernel_majorant g ha
  have hcont : ContinuousOn (fun z : Real × (M × M) => heatKernel g z.1 z.2.1 z.2.2)
      (Set.Ioi (q.1 / 2) ×ˢ Set.univ) := by
    apply continuousOn_tsum
    · intro i
      exact ((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
        ((scalarEigenFunction g i).smooth.continuous.comp continuous_snd.fst)).mul
          ((scalarEigenFunction g i).smooth.continuous.comp continuous_snd.snd) |>.continuousOn
    · exact hb
    · intro i z hz
      exact hbound i z.1 hz.1.le z.2.1 z.2.2
  have hq' : q ∈ Set.Ioi (q.1 / 2) ×ˢ Set.univ := by
    constructor
    · change q.1 / 2 < q.1
      exact half_lt_self (show 0 < q.1 from hq.1)
    · exact Set.mem_univ _
  exact (hcont.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hq')).continuousWithinAt

open Filter Set in
open scoped Topology in
theorem tendstoUniformly_heatKernel_sub
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t) (x : M) :
    TendstoUniformly (fun s y => heatKernel g (t - s) x y) (heatKernel g t x)
      (𝓝[>] (0 : ℝ)) := by
  have hU : Iio t ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds ht
  have hmap : Continuous (fun z : ℝ × M => (t - z.1, (x, z.2))) := by
    fun_prop
  have hcont : ContinuousOn (fun z : ℝ × M => heatKernel g (t - z.1) x z.2)
      (Iio t ×ˢ univ) := by
    apply (continuousOn_heatKernel g).comp hmap.continuousOn
    intro z hz
    change 0 < t - z.1 ∧ True
    exact ⟨sub_pos.mpr hz.1, trivial⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨v, hv, hvu⟩ := isCompact_univ.mem_uniformity_of_prod
    (f := fun s y => heatKernel g (t - s) x y)
    (s := Iio t) (q := (0 : ℝ)) hcont (mem_Iio.mpr ht)
    (Metric.dist_mem_uniformity (α := ℝ) hε)
  have hv' : v ∈ 𝓝 (0 : ℝ) := by
    rwa [nhdsWithin_eq_nhds.mpr hU] at hv
  filter_upwards [mem_nhdsWithin_of_mem_nhds hv'] with s hs
  intro y
  simpa only [Set.mem_ofPred_eq, sub_zero, dist_comm] using hvu s hs y (mem_univ y)

theorem integral_mul_heatKernel_diagonal (g : SmoothRiemannianMetric I M)
    {t : Real} (ht : 0 < t) {w : M → Real}
    (hw : Integrable w (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (∫ x, w x * heatKernel g t x x ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      ∑' i : TensorEigenIdx (I := I) (M := M) g 0 0,
        Real.exp (-TensorEigenIdx.lambda i * t) *
          ∫ x, w x * (scalarEigenFunction g i).toFun x ^ 2
            ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  let : Countable (TensorEigenIdx (I := I) (M := M) g 0 0) :=
    Parabolic.MaximalRegularity.countable_tensorEigenIdx
      (tensorResolventL2_isCompactOperator g 0 0)
  obtain ⟨b, hb, hbound⟩ := exists_summable_heatKernel_majorant g ht
  let K := fun (i : TensorEigenIdx (I := I) (M := M) g 0 0) (x : M) =>
    Real.exp (-TensorEigenIdx.lambda i * t) * (scalarEigenFunction g i).toFun x *
      (scalarEigenFunction g i).toFun x
  let F := fun i x => w x * K i x
  have hK (i : TensorEigenIdx (I := I) (M := M) g 0 0) : Continuous (K i) :=
    ((scalarEigenFunction g i).smooth.continuous.const_mul _).mul
      (scalarEigenFunction g i).smooth.continuous
  have hF (i : TensorEigenIdx (I := I) (M := M) g 0 0) :
      Integrable (F i) (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hw.mul_bdd (hK i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hbound i t le_rfl x x)
  have hFnorm : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 0 =>
      ∫ x, ‖F i x‖ ∂riemannianVolumeMeasure (I := I) (M := M) g) := by
    apply Summable.of_nonneg_of_le (fun i => integral_nonneg fun x => norm_nonneg (F i x))
      (fun i => ?_) (hb.mul_left (∫ x, ‖w x‖ ∂riemannianVolumeMeasure (I := I) (M := M) g))
    calc
      (∫ x, ‖F i x‖ ∂riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ∫ x, ‖w x‖ * b i ∂riemannianVolumeMeasure (I := I) (M := M) g := by
        apply integral_mono (hF i).norm (hw.norm.mul_const (b i))
        intro x
        change ‖w x * K i x‖ ≤ ‖w x‖ * b i
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hbound i t le_rfl x x) (norm_nonneg _)
      _ = _ := integral_mul_const _ _
  have hinter := integral_tsum_of_summable_integral_norm hF hFnorm
  have hpoint (x : M) : w x * heatKernel g t x x = ∑' i, F i x := by
    simp only [heatKernel, ← tsum_mul_left]
    rfl
  calc
    _ = ∫ x, (∑' i, F i x) ∂riemannianVolumeMeasure (I := I) (M := M) g :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑' i, ∫ x, F i x ∂riemannianVolumeMeasure (I := I) (M := M) g := hinter.symm
    _ = _ := by
      apply tsum_congr
      intro i
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by dsimp only [F, K]; ring

theorem integral_heatKernel_mul (g : SmoothRiemannianMetric I M)
    {t : Real} (ht : 0 < t) {w : M → Real}
    (hw : Integrable w (riemannianVolumeMeasure (I := I) (M := M) g)) (x : M) :
    (∫ y, heatKernel g t x y * w y ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      ∑' i : TensorEigenIdx (I := I) (M := M) g 0 0,
        Real.exp (-TensorEigenIdx.lambda i * t) * (scalarEigenFunction g i).toFun x *
          ∫ y, (scalarEigenFunction g i).toFun y * w y
            ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  let : Countable (TensorEigenIdx (I := I) (M := M) g 0 0) :=
    Parabolic.MaximalRegularity.countable_tensorEigenIdx
      (tensorResolventL2_isCompactOperator g 0 0)
  obtain ⟨b, hb, hbound⟩ := exists_summable_heatKernel_majorant g ht
  let K := fun (i : TensorEigenIdx (I := I) (M := M) g 0 0) (y : M) =>
    Real.exp (-TensorEigenIdx.lambda i * t) * (scalarEigenFunction g i).toFun x *
      (scalarEigenFunction g i).toFun y
  let F := fun i y => K i y * w y
  have hK (i : TensorEigenIdx (I := I) (M := M) g 0 0) : Continuous (K i) :=
    (scalarEigenFunction g i).smooth.continuous.const_mul _
  have hF (i : TensorEigenIdx (I := I) (M := M) g 0 0) :
      Integrable (F i) (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hw.bdd_mul (hK i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hbound i t le_rfl x y)
  have hFnorm : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 0 =>
      ∫ y, ‖F i y‖ ∂riemannianVolumeMeasure (I := I) (M := M) g) := by
    apply Summable.of_nonneg_of_le (fun i => integral_nonneg fun y => norm_nonneg (F i y))
      (fun i => ?_) (hb.mul_right (∫ y, ‖w y‖ ∂riemannianVolumeMeasure (I := I) (M := M) g))
    calc
      (∫ y, ‖F i y‖ ∂riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ∫ y, b i * ‖w y‖ ∂riemannianVolumeMeasure (I := I) (M := M) g := by
        apply integral_mono (hF i).norm (hw.norm.const_mul (b i))
        intro y
        change ‖K i y * w y‖ ≤ b i * ‖w y‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound i t le_rfl x y) (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  have hinter := integral_tsum_of_summable_integral_norm hF hFnorm
  have hpoint (y : M) : heatKernel g t x y * w y = ∑' i, F i y := by
    simp only [heatKernel, ← tsum_mul_right]
    rfl
  calc
    _ = ∫ y, (∑' i, F i y) ∂riemannianVolumeMeasure (I := I) (M := M) g :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑' i, ∫ y, F i y ∂riemannianVolumeMeasure (I := I) (M := M) g := hinter.symm
    _ = _ := by
      apply tsum_congr
      intro i
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by dsimp only [F, K]; ring

end DifferentialGeometry.Analysis.HeatEquation
