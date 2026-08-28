import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H1H2OperatorFieldComposition

import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricLoweringTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.JetTowerComparison

set_option autoImplicit false

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def l6VolC (Λ : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (Λ ^ n) ^ (1 / 6 : ℝ)

lemma l6VolC_nonneg (Λ : ℝ) (n : ℕ) : 0 ≤ l6VolC Λ n :=
  Real.rpow_nonneg (Real.sqrt_nonneg _) _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
private theorem lpNorm_vol_cross
    (gBase g : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ)
    (f : M → ℝ) (hf : Continuous f) :
    lpNorm f 6 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      l6VolC Λ (Module.finrank ℝ E) *
        lpNorm f 6 (riemannianVolumeMeasure (I := I) (M := M) gBase) := by
  let μB := riemannianVolumeMeasure (I := I) (M := M) gBase
  let μg := riemannianVolumeMeasure (I := I) (M := M) g
  let L : ℝ := Real.sqrt (Λ ^ Module.finrank ℝ E)
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  let : IsFiniteMeasure μB :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) gBase
  have hfB : MemLp f 6 μB :=
    hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hμ : μg ≤ ENNReal.ofReal L • μB := by
    simpa only [μg, μB, L] using
      (volumeMeasure_cross_le (I := I) (M := M) gBase g hEq).1
  have he := eLpNorm_mono_measure (p := (6 : ENNReal)) f hμ
  rw [eLpNorm_smul_measure_of_ne_top (μ := μB) (p := (6 : ENNReal))
      (by norm_num) f (ENNReal.ofReal L), smul_eq_mul] at he
  have hexp : (1 / (6 : ENNReal)).toReal = (1 / 6 : ℝ) := by norm_num
  rw [hexp] at he
  have hpow : (ENNReal.ofReal L) ^ (1 / 6 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have htop := ENNReal.mul_ne_top hpow hfB.eLpNorm_ne_top
  have hr := ENNReal.toReal_mono htop he
  rw [toReal_eLpNorm hf.aestronglyMeasurable,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hL,
    toReal_eLpNorm hf.aestronglyMeasurable] at hr
  simpa only [μg, μB, L, l6VolC] using hr

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem fiber0_cont
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s) :
    Continuous (fun x => Real.sqrt
      (riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (T.toSection x))) := by
  apply Real.continuous_sqrt.comp
  have hinner := SmoothCcTensor.continuous_inner_self (I := I) (M := M) T
  refine hinner.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise
    (I := I) (M := M) g 0 s x (T.toSection x),
    ← SmoothCcTensor.toFun_apply (I := I) (M := M) T x]

theorem h1Lp6RS_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
        ∀ S : SmoothCcTensorH1 g r s,
          lpNorm (fun x => Real.sqrt
              (riemannianFiberNormSq (I := I) (M := M) g r s x
                (S.toCcTensor.toSection x))) 6
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤ C * ‖S‖ := by
  classical
  obtain ⟨Cb, hCb, hbaseLp⟩ :=
    h1_lp6_fiber_rs (I := I) (M := M) hDim gBase 0 (r + s)
  let q : ℝ := Real.sqrt (Λ ^ (r + s))
  let V : ℝ := l6VolC Λ (Module.finrank ℝ E)
  let K : ℝ := kjetOneC (Module.finrank ℝ E) Λ Λ (r + s)
  let C : ℝ := q * V * Cb * (4 * K)
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hV : 0 ≤ V := l6VolC_nonneg _ _
  have hK : 0 ≤ K := kjetOneC_nonneg hΛ0 _ _
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro g hEq hjet S
  let : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let L : SmoothCcTensor g 0 (r + s) :=
    lowerCc (I := I) (M := M) g r s S.toCcTensor
  let LB : SmoothCcTensor gBase 0 (r + s) := L.recast (g' := gBase)
  let SB : SmoothCcTensorH1 gBase 0 (r + s) := ⟨LB⟩
  let J : ℝ := ∑ k ∈ Finset.range 2,
    ‖iteratedCovGrad (I := I) g 0 (r + s) k L‖
  have hJ : 0 ≤ J := Finset.sum_nonneg (fun k _ => norm_nonneg _)
  have hb0 : ‖LB‖ ≤ K * J := by
    simpa only [LB, K, J, iteratedCovGrad_zero] using
      (jetCross_l2_one (I := I) gBase g hEq hjet hΛ0 (r + s) L
        (j := 0) (by norm_num))
  have hb1 : ‖covGrad (I := I) (M := M) gBase 0 (r + s) LB‖ ≤ K * J := by
    simpa only [LB, K, J, iteratedCovGrad_succ, iteratedCovGrad_zero,
      Nat.add_zero] using
      (jetCross_l2_one (I := I) gBase g hEq hjet hΛ0 (r + s) L
        (j := 1) (by norm_num))
  have hSBsq := smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) gBase 0 (r + s) LB
  have hSBsum : ‖SB‖ ≤ ‖LB‖ +
      ‖covGrad (I := I) (M := M) gBase 0 (r + s) LB‖ := by
    have hsq : ‖SB‖ ^ 2 ≤
        (‖LB‖ + ‖covGrad (I := I) (M := M) gBase 0 (r + s) LB‖) ^ 2 := by
      rw [show ‖SB‖ ^ 2 = ‖LB‖ ^ 2 +
          ‖covGrad (I := I) (M := M) gBase 0 (r + s) LB‖ ^ 2 from hSBsq]
      nlinarith [mul_nonneg (norm_nonneg LB)
        (norm_nonneg (covGrad (I := I) (M := M) gBase 0 (r + s) LB))]
    exact (abs_le_of_sq_le_sq' hsq (add_nonneg (norm_nonneg _)
      (norm_nonneg _))).2
  have hSBJ : ‖SB‖ ≤ 2 * K * J := by
    have hKJ : 0 ≤ K * J := mul_nonneg hK hJ
    calc
      ‖SB‖ ≤ ‖LB‖ +
          ‖covGrad (I := I) (M := M) gBase 0 (r + s) LB‖ := hSBsum
      _ ≤ K * J + K * J := add_le_add hb0 hb1
      _ = 2 * K * J := by ring
  have hL0 := lowerCc_jet_norm (I := I) (M := M) g r s 0 S.toCcTensor (by norm_num)
  have hL1 := lowerCc_jet_norm (I := I) (M := M) g r s 1 S.toCcTensor (by norm_num)
  have hL0' : ‖L‖ = ‖S.toCcTensor‖ := by
    simpa only [L, iteratedCovGrad_zero] using hL0
  have hL1' : ‖covGrad (I := I) (M := M) g 0 (r + s) L‖ =
      ‖covGrad (I := I) (M := M) g r s S.toCcTensor‖ := by
    simpa only [L, iteratedCovGrad_succ, iteratedCovGrad_zero,
      Nat.add_zero] using hL1
  have hJshape : J = ‖S.toCcTensor‖ +
      ‖covGrad (I := I) (M := M) g r s S.toCcTensor‖ := by
    simp only [J, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero]
    rw [hL0', hL1']
  have hS0 : ‖S.toCcTensor‖ ≤ ‖S‖ :=
    SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S
  have hSsq := smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g r s S.toCcTensor
  have hS1 : ‖covGrad (I := I) (M := M) g r s S.toCcTensor‖ ≤ ‖S‖ := by
    have hsq : ‖covGrad (I := I) (M := M) g r s S.toCcTensor‖ ^ 2 ≤ ‖S‖ ^ 2 := by
      rw [hSsq]
      nlinarith [sq_nonneg ‖S.toCcTensor‖]
    exact (abs_le_of_sq_le_sq' hsq (norm_nonneg S)).2
  have hJS : J ≤ 2 * ‖S‖ := by
    rw [hJshape]
    linarith
  have hSB : ‖SB‖ ≤ 4 * K * ‖S‖ := by
    calc
      ‖SB‖ ≤ 2 * K * J := hSBJ
      _ ≤ 2 * K * (2 * ‖S‖) :=
        mul_le_mul_of_nonneg_left hJS (mul_nonneg (by norm_num) hK)
      _ = 4 * K * ‖S‖ := by ring
  let fg : M → ℝ := fun x => Real.sqrt
    (riemannianFiberNormSq (I := I) (M := M) g r s x
      (S.toCcTensor.toSection x))
  let fb : M → ℝ := fun x => Real.sqrt
    (riemannianFiberNormSq (I := I) (M := M) gBase 0 (r + s) x
      (LB.toSection x))
  have hfb : Continuous fb := fiber0_cont (I := I) gBase (r + s) LB
  have hpt : ∀ x, fg x ≤ q * fb x := by
    intro x
    have hsquare := fibreNormSq_cross_le (I := I) (M := M) gBase g hΛ
      (fun y v => hEq.2 y (Set.mem_univ y) v) (r + s) x L
    have hsqrt := Real.sqrt_le_sqrt hsquare
    rw [Real.sqrt_mul (pow_nonneg hΛ0 _)] at hsqrt
    rw [lowerCc_riemannianFiberNormSq (I := I) (M := M) g r s S.toCcTensor x] at hsqrt
    simpa only [fg, fb, q, LB] using hsqrt
  have hupper : MemLp (fun x => q * fb x) 6
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (continuous_const.mul hfb).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hptLp : lpNorm fg 6 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      q * lpNorm fb 6 (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hmono : lpNorm fg 6 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        lpNorm (fun x => q * fb x) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) := by
      apply lpNorm_mono_real hupper
      intro x
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact hpt x
    calc
      lpNorm fg 6 (riemannianVolumeMeasure (I := I) (M := M) g)
          ≤ lpNorm (fun x => q * fb x) 6
              (riemannianVolumeMeasure (I := I) (M := M) g) := hmono
      _ = q * lpNorm fb 6 (riemannianVolumeMeasure (I := I) (M := M) g) := by
        rw [show (fun x => q * fb x) = q • fb from by funext x; simp,
          lpNorm_const_smul]
        simp [Real.norm_eq_abs, abs_of_nonneg hq]
  have hvol := lpNorm_vol_cross (I := I) gBase g hEq fb hfb
  have hbase := hbaseLp SB
  calc
    lpNorm (fun x => Real.sqrt
        (riemannianFiberNormSq (I := I) (M := M) g r s x
          (S.toCcTensor.toSection x))) 6
        (riemannianVolumeMeasure (I := I) (M := M) g)
        = lpNorm fg 6 (riemannianVolumeMeasure (I := I) (M := M) g) := rfl
    _ ≤ q * lpNorm fb 6 (riemannianVolumeMeasure (I := I) (M := M) g) := hptLp
    _ ≤ q * (V * lpNorm fb 6
        (riemannianVolumeMeasure (I := I) (M := M) gBase)) :=
      mul_le_mul_of_nonneg_left (by simpa only [V] using hvol) hq
    _ ≤ q * (V * (Cb * ‖SB‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by simpa only [fb, SB] using hbase) hV) hq
    _ ≤ q * (V * (Cb * (4 * K * ‖S‖))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hSB hCb) hV) hq
    _ = C * ‖S‖ := by simp only [C]; ring

end RicciFlow
end PDE
end DifferentialGeometry

end
