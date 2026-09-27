import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Compactness.Basic
import DifferentialGeometry.Analysis.Integration.Measure.AddCircle
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuous
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.ScalarNorm
import Mathlib.Topology.Sequences

noncomputable section

open scoped Manifold ContDiff Topology InnerProductSpace
open Set MeasureTheory Filter

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem norm_sq_eq_integral_scalar0_sq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S : SmoothCcTensor g 0 0) :
    ‖S‖ ^ 2 = ∫ z, (TensorRSField.scalar0 S.toSection z) ^ 2
      ∂riemannianVolumeMeasure (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g := by
  rw [← real_inner_self_eq_norm_sq, SmoothCcTensor.inner_eq_integral_scalar0_mul]
  simp only [pow_two]

private theorem exists_scalar0_sub_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensor g 0 0) (x y : ℝ),
      x ∈ Icc (0 : ℝ) 1 → y ∈ Icc (0 : ℝ) 1 →
      |TensorRSField.scalar0 S.toSection (x : AddCircle (1 : ℝ)) -
        TensorRSField.scalar0 S.toSection (y : AddCircle (1 : ℝ))| ≤
        C * ‖parameterDerivativeCcTensor g S‖ * Real.sqrt |x - y| := by
  obtain ⟨K, hK, hbound⟩ := exists_integral_comp_coe_le_mul_riemannianVolumeMeasure g
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, ?_⟩
  intro S x y hx hy
  let f : ℝ → ℝ := fun x => TensorRSField.scalar0 S.toSection (x : AddCircle (1 : ℝ))
  have hf : ContDiff ℝ ∞ f :=
    contMDiff_iff_contDiff.mp ((TensorRSField.scalar0_smooth S.toSection).comp contMDiff_coe)
  have hf1 : ContDiffOn ℝ 1 f (Icc 0 1) := (hf.of_le (by decide)).contDiffOn
  let u := timeH1.ofContDiffOn (by norm_num : (0 : ℝ) ≤ 1) f hf1
  have hu : EqOn u.toFun f (Icc 0 1) := timeH1.toFun_ofContDiffOn (by norm_num) f hf1
  have hderiv : ‖u.deriv‖ = Real.sqrt (∫ s in Icc (0 : ℝ) 1, ‖deriv f s‖ ^ 2) := by
    rw [norm_eq_sqrt_integral]
    congr 1
    apply integral_congr_ae
    filter_upwards [timeH1.deriv_ofContDiffOn (by norm_num : (0 : ℝ) ≤ 1) f hf1] with s hs
    exact congrArg (fun z => ‖z‖ ^ 2) hs
  have hdf : deriv f = fun s : ℝ =>
      TensorRSField.scalar0 (parameterDerivativeCcTensor g S).toSection (s : AddCircle (1 : ℝ)) := by
    funext s
    exact (scalar0_parameterDerivativeCcTensor_coe g S s).symm
  have hint := hbound (fun z => (TensorRSField.scalar0
    (parameterDerivativeCcTensor g S).toSection z) ^ 2)
    ((TensorRSField.scalar0_smooth (parameterDerivativeCcTensor g S).toSection).continuous.pow 2)
    (fun z => sq_nonneg _)
  have hd : ‖u.deriv‖ ≤ Real.sqrt K * ‖parameterDerivativeCcTensor g S‖ := by
    rw [hderiv, hdf]
    simp only [Real.norm_eq_abs, sq_abs]
    calc
      _ ≤ Real.sqrt (K * ‖parameterDerivativeCcTensor g S‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        simpa only [← norm_sq_eq_integral_scalar0_sq] using hint
      _ = _ := by rw [Real.sqrt_mul hK.le, Real.sqrt_sq (norm_nonneg _)]
  have h := u.toFun_sub_le hy hx
  rw [hu hx, hu hy, Real.norm_eq_abs] at h
  exact h.trans ((mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg _)).trans_eq (by ring))


theorem exists_scalarH1ToContinuous_coe_sub_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : TensorHs g 0 0 1) (x y : ℝ),
      x ∈ Icc (0 : ℝ) 1 → y ∈ Icc (0 : ℝ) 1 →
      |(scalarH1ToContinuous g u) (x : AddCircle (1 : ℝ)) -
        (scalarH1ToContinuous g u) (y : AddCircle (1 : ℝ))| ≤
        C * ‖u‖ * Real.sqrt |x - y| := by
  obtain ⟨C, hC, hcore⟩ := exists_scalar0_sub_le g
  obtain ⟨A, hA, hjet⟩ := hsJet_le g 0 0
  let D := ‖parameterDerivativeHs g 0‖
  have hD : 0 ≤ D := norm_nonneg _
  have hnormeq {a b : ℝ} (h : a = b) (S : SmoothCcTensor g 0 0) :
      ‖ccTensorToHs g 0 a S‖ = ‖ccTensorToHs g 0 b S‖ := by
    subst b
    rfl
  have hderiv (S : SmoothCcTensor g 0 0) :
      ‖parameterDerivativeCcTensor g S‖ ≤ A * D * ‖ccTensorToHs g 0 1 S‖ := by
    have hd := (parameterDerivativeHs g 0).le_opNorm (ccTensorToHs g 0 ((0 : ℕ) + 1) S)
    rw [parameterDerivativeHs_apply_ccTensorToHs] at hd
    rw [hnormeq (by norm_num : ((0 : ℕ) : ℝ) = 0),
      hnormeq (by norm_num : ((0 : ℕ) : ℝ) + 1 = 1)] at hd
    have hj := hjet (parameterDerivativeCcTensor g S)
    norm_num only [Nat.zero_add, Finset.sum_range_one,
      DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_zero] at hj
    rw [hnormeq (by norm_num : ((0 : ℕ) : ℝ) = 0)] at hj
    exact hj.trans ((mul_le_mul_of_nonneg_left hd hA).trans_eq (by dsimp only [D]; ring))
  have hcore' (S : SmoothCcTensor g 0 0) (x y : ℝ)
      (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
      |scalarH1ToContinuous g (ccTensorToHs g 0 1 S) (x : AddCircle (1 : ℝ)) -
          scalarH1ToContinuous g (ccTensorToHs g 0 1 S) (y : AddCircle (1 : ℝ))| ≤
        (C * A * D) * ‖ccTensorToHs g 0 1 S‖ * Real.sqrt |x - y| := by
    rw [scalarH1ToContinuous_apply_ccTensorToHs,
      scalarH1ToContinuous_apply_ccTensorToHs]
    exact (hcore S x y hx hy).trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hderiv S) hC) (Real.sqrt_nonneg _)).trans_eq (by ring))
  refine ⟨C * A * D, by positivity, ?_⟩
  intro u x y hx hy
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp
    (ccToHsLin_dense g 0 (by norm_num : (0 : ℝ) ≤ 1) u)
  choose S hS using hv
  have hleft : Tendsto (fun i => |scalarH1ToContinuous g (v i) (x : AddCircle (1 : ℝ)) -
      scalarH1ToContinuous g (v i) (y : AddCircle (1 : ℝ))|) atTop
      (𝓝 (|(scalarH1ToContinuous g u) (x : AddCircle (1 : ℝ)) -
        (scalarH1ToContinuous g u) (y : AddCircle (1 : ℝ))|)) := by
    have heval (z : AddCircle (1 : ℝ)) :
        Tendsto (fun i => scalarH1ToContinuous g (v i) z) atTop
          (𝓝 (scalarH1ToContinuous g u z)) :=
      ((ContinuousMap.evalCLM ℝ z).continuous.tendsto
        (scalarH1ToContinuous g u)).comp
          (((scalarH1ToContinuous g).continuous.tendsto u).comp hvlim)
    exact ((heval (x : AddCircle (1 : ℝ))).sub (heval (y : AddCircle (1 : ℝ)))).abs
  have hright : Tendsto (fun i => (C * A * D) * ‖v i‖ * Real.sqrt |x - y|) atTop
      (𝓝 ((C * A * D) * ‖u‖ * Real.sqrt |x - y|)) := by
    exact ((tendsto_const_nhds.mul hvlim.norm).mul tendsto_const_nhds)
  apply le_of_tendsto_of_tendsto hleft hright
  apply Eventually.of_forall
  intro i
  dsimp only
  rw [← hS i]
  exact hcore' (S i) x y hx hy

theorem exists_scalarH1PiToContinuous_coe_sub_le {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) (x y : ℝ),
      x ∈ Icc (0 : ℝ) 1 → y ∈ Icc (0 : ℝ) 1 →
      ‖scalarH1PiToContinuous g u (x : AddCircle (1 : ℝ)) -
        scalarH1PiToContinuous g u (y : AddCircle (1 : ℝ))‖ ≤
        C * ‖u‖ * Real.sqrt |x - y| := by
  obtain ⟨C, hC, hscalar⟩ := exists_scalarH1ToContinuous_coe_sub_le g
  refine ⟨C, hC, ?_⟩
  intro u x y hx hy
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change |scalarH1ToContinuous g (u i) (x : AddCircle (1 : ℝ)) -
    scalarH1ToContinuous g (u i) (y : AddCircle (1 : ℝ))| ≤ _
  exact (hscalar (u i) x y hx hy).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u i) hC) (Real.sqrt_nonneg _))

end AddCircle
