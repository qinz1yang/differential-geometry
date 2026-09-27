import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Agmon
import DifferentialGeometry.Analysis.Integration.Measure.AddCircle
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuous
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothInclusion
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.ScalarNorm
import Mathlib.Topology.Sequences

open scoped Manifold ContDiff Topology InnerProductSpace
open Set MeasureTheory Filter

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem norm_sq_eq_integral_scalar0_sq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S : SmoothCcTensor g 0 0) :
    ‖S‖ ^ 2 = ∫ z, (TensorRSField.scalar0 S.toSection z) ^ 2
      ∂riemannianVolumeMeasure (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g := by
  rw [← real_inner_self_eq_norm_sq, SmoothCcTensor.inner_eq_integral_scalar0_mul]
  simp only [pow_two]

private theorem exists_agmon_ccTensor
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensor g 0 0) (z : AddCircle (1 : ℝ)),
      |TensorRSField.scalar0 S.toSection z| ^ 2 ≤
        C * ‖S‖ * (‖S‖ + ‖parameterDerivativeCcTensor g S‖) := by
  obtain ⟨K, hK, hbound⟩ := exists_integral_comp_coe_le_mul_riemannianVolumeMeasure g
  have hint (S : SmoothCcTensor g 0 0) :
      (∫ x in Icc (0 : ℝ) 1, |TensorRSField.scalar0 S.toSection (x : AddCircle (1 : ℝ))| ^ 2)
        ≤ K * ‖S‖ ^ 2 := by
    have h := hbound (fun z => (TensorRSField.scalar0 S.toSection z) ^ 2)
      ((TensorRSField.scalar0_smooth S.toSection).continuous.pow 2) (fun z => sq_nonneg _)
    simpa only [sq_abs, ← norm_sq_eq_integral_scalar0_sq] using h
  have hsqrt (S : SmoothCcTensor g 0 0) :
      Real.sqrt (∫ x in Icc (0 : ℝ) 1,
        |TensorRSField.scalar0 S.toSection (x : AddCircle (1 : ℝ))| ^ 2)
        ≤ Real.sqrt K * ‖S‖ := by
    calc
      _ ≤ Real.sqrt (K * ‖S‖ ^ 2) := Real.sqrt_le_sqrt (hint S)
      _ = _ := by rw [Real.sqrt_mul hK.le, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨2 * K, by positivity, ?_⟩
  intro S z
  let f : ℝ → ℝ := fun x => TensorRSField.scalar0 S.toSection (x : AddCircle (1 : ℝ))
  have hf : ContDiff ℝ ∞ f :=
    contMDiff_iff_contDiff.mp ((TensorRSField.scalar0_smooth S.toSection).comp contMDiff_coe)
  obtain ⟨x, hx, hxeq⟩ := (show z ∈ (fun x : ℝ => (x : AddCircle (1 : ℝ))) '' Ioc 0 1 from by
    rw [show (fun x : ℝ => (x : AddCircle (1 : ℝ))) '' Ioc 0 1 = univ by
      simpa only [zero_add] using AddCircle.coe_image_Ioc_eq (1 : ℝ) (0 : ℝ)]
    exact mem_univ z)
  have hag := (hf.of_le (by decide : (1 : ℕ∞ω) ≤ ∞)).contDiffOn.agmon_inequality
    (by norm_num : (0 : ℝ) < 1) (Ioc_subset_Icc_self hx)
  have hdf : deriv f = fun x : ℝ =>
      TensorRSField.scalar0 (parameterDerivativeCcTensor g S).toSection (x : AddCircle (1 : ℝ)) := by
    funext x
    exact (scalar0_parameterDerivativeCcTensor_coe g S x).symm
  simp only [div_one, Real.norm_eq_abs, hdf, f, hxeq] at hag
  have hprod :
      Real.sqrt (∫ s in Icc (0 : ℝ) 1, |TensorRSField.scalar0 S.toSection (s : AddCircle (1 : ℝ))| ^ 2) *
        Real.sqrt (∫ s in Icc (0 : ℝ) 1,
          |TensorRSField.scalar0 (parameterDerivativeCcTensor g S).toSection (s : AddCircle (1 : ℝ))| ^ 2)
      ≤ K * ‖S‖ * ‖parameterDerivativeCcTensor g S‖ := by
    calc
      _ ≤ (Real.sqrt K * ‖S‖) * (Real.sqrt K * ‖parameterDerivativeCcTensor g S‖) :=
        mul_le_mul (hsqrt S) (hsqrt (parameterDerivativeCcTensor g S))
          (Real.sqrt_nonneg _) (by positivity)
      _ = (Real.sqrt K) ^ 2 * ‖S‖ * ‖parameterDerivativeCcTensor g S‖ := by ring
      _ = _ := by rw [Real.sq_sqrt hK.le]
  have hi := hint S
  nlinarith [mul_nonneg hK.le (sq_nonneg ‖S‖)]

private theorem exists_agmon_ccTensor_spectral
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensor g 0 0) (z : AddCircle (1 : ℝ)),
      |TensorRSField.scalar0 S.toSection z| ^ 2 ≤
        C * ‖ccTensorToHs g 0 0 S‖ * ‖ccTensorToHs g 0 1 S‖ := by
  obtain ⟨K, hK, hbound⟩ := exists_agmon_ccTensor g
  obtain ⟨A, hA, hjet⟩ := hsJet_le g 0 0
  have hnormeq {a b : ℝ} (h : a = b) (S : SmoothCcTensor g 0 0) :
      ‖ccTensorToHs g 0 a S‖ = ‖ccTensorToHs g 0 b S‖ := by
    subst b
    rfl
  have hl2 (S : SmoothCcTensor g 0 0) : ‖S‖ ≤ A * ‖ccTensorToHs g 0 0 S‖ := by
    have h := hjet S
    norm_num only [Nat.zero_add, Finset.sum_range_one,
      DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_zero] at h
    rw [hnormeq (by norm_num : ((0 : ℕ) : ℝ) = 0)] at h
    exact h
  let D := ‖parameterDerivativeHs g 0‖
  have hD : 0 ≤ D := norm_nonneg _
  have hderiv (S : SmoothCcTensor g 0 0) :
      ‖parameterDerivativeCcTensor g S‖ ≤ A * D * ‖ccTensorToHs g 0 1 S‖ := by
    have hd := (parameterDerivativeHs g 0).le_opNorm (ccTensorToHs g 0 ((0 : ℕ) + 1) S)
    rw [parameterDerivativeHs_apply_ccTensorToHs] at hd
    rw [hnormeq (by norm_num : ((0 : ℕ) : ℝ) = 0),
      hnormeq (by norm_num : ((0 : ℕ) : ℝ) + 1 = 1)] at hd
    exact (hl2 (parameterDerivativeCcTensor g S)).trans
      ((mul_le_mul_of_nonneg_left hd hA).trans_eq (by dsimp only [D]; ring))
  refine ⟨K * A * (A * (1 + D)), by positivity, ?_⟩
  intro S z
  have hlo := ccToHs_norm_mono g 0 (by norm_num : (0 : ℝ) ≤ 1) S
  have hsum : ‖S‖ + ‖parameterDerivativeCcTensor g S‖ ≤
      (A * (1 + D)) * ‖ccTensorToHs g 0 1 S‖ := by
    have hval := (hl2 S).trans (mul_le_mul_of_nonneg_left hlo hA)
    nlinarith [hderiv S]
  calc
    _ ≤ K * ‖S‖ * (‖S‖ + ‖parameterDerivativeCcTensor g S‖) := hbound S z
    _ ≤ K * (A * ‖ccTensorToHs g 0 0 S‖) *
        ((A * (1 + D)) * ‖ccTensorToHs g 0 1 S‖) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hl2 S) hK
      · exact hsum
      · positivity
      · positivity
    _ = _ := by ring

theorem exists_norm_scalarH1ToContinuous_sq_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : TensorHs g 0 0 1,
      ‖scalarH1ToContinuous g u‖ ^ 2 ≤
        C * ‖tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (0 : ℝ) ≤ 1) u‖ * ‖u‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_agmon_ccTensor_spectral g
  refine ⟨C, hC, ?_⟩
  intro u
  let L := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ 1)
  have hpoint (z : AddCircle (1 : ℝ)) :
      |scalarH1ToContinuous g u z| ^ 2 ≤ C * ‖L u‖ * ‖u‖ := by
    obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp
      (ccToHsLin_dense g 0 (by norm_num : (0 : ℝ) ≤ 1) u)
    choose S hS using hv
    have hcore (i : ℕ) : v i = ccTensorToHs g 0 1 (S i) := (hS i).symm
    have hleft : Tendsto (fun i => |scalarH1ToContinuous g (v i) z| ^ 2)
        atTop (𝓝 (|scalarH1ToContinuous g u z| ^ 2)) := by
      exact (((ContinuousMap.evalCLM ℝ z).continuous.tendsto
        (scalarH1ToContinuous g u)).comp
          (((scalarH1ToContinuous g).continuous.tendsto u).comp hvlim)).abs.pow 2
    have hright : Tendsto (fun i => C * ‖L (v i)‖ * ‖v i‖) atTop
        (𝓝 (C * ‖L u‖ * ‖u‖)) :=
      (tendsto_const_nhds.mul (((L.continuous.tendsto u).comp hvlim).norm)).mul hvlim.norm
    apply le_of_tendsto_of_tendsto hleft hright
    apply Eventually.of_forall
    intro i
    dsimp only
    rw [hcore, scalarH1ToContinuous_apply_ccTensorToHs]
    simpa only [L, tensorHsInclusion_ccTensorToHs] using hbound (S i) z
  have hnonneg : 0 ≤ C * ‖L u‖ * ‖u‖ := by positivity
  have hsup : ‖scalarH1ToContinuous g u‖ ≤ Real.sqrt (C * ‖L u‖ * ‖u‖) := by
    apply (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).mpr
    intro z
    rw [Real.norm_eq_abs]
    exact (Real.le_sqrt (abs_nonneg _) hnonneg).mpr (hpoint z)
  nlinarith [Real.sq_sqrt hnonneg, norm_nonneg (scalarH1ToContinuous g u)]


theorem exists_norm_scalarH1PiToContinuous_sq_le {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PiLp 2 (fun _ : ι => TensorHs g 0 0 1),
      ‖scalarH1PiToContinuous g u‖ ^ 2 ≤ C *
        ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0) (by norm_num : (0 : ℝ) ≤ 1)) u‖ * ‖u‖ := by
  obtain ⟨C, hC, hscalar⟩ := exists_norm_scalarH1ToContinuous_sq_le g
  refine ⟨C, hC, ?_⟩
  intro u
  let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0) (by norm_num : (0 : ℝ) ≤ 1))
  have hpos : 0 ≤ C * ‖L u‖ * ‖u‖ := by positivity
  have hb : ‖scalarH1PiToContinuous g u‖ ≤ Real.sqrt (C * ‖L u‖ * ‖u‖) := by
    apply (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).mpr
    intro z
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (Real.le_sqrt (norm_nonneg _) hpos).mpr
    have h1 : ‖scalarH1ToContinuous g (u i) z‖ ^ 2 ≤ ‖scalarH1ToContinuous g (u i)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (ContinuousMap.norm_coe_le_norm _ z) 2
    have h2 := h1.trans (hscalar (u i))
    change ‖scalarH1ToContinuous g (u i) z‖ ^ 2 ≤ _
    refine h2.trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (L u) i) hC)
      (PiLp.norm_apply_le u i) (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))
  exact (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans_eq (Real.sq_sqrt hpos)

end AddCircle
