import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.WeightedDivergence
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.IntegrationByParts
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricContinuity

noncomputable section

namespace DifferentialGeometry.Analysis.Elliptic

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow (metricNabla0S covDiv0SField innerPt_eq_inner0S)
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless] [SigmaCompactSpace M]

theorem integral_sq_weighted_covDiv0SField_le_of_hasCompactSupport
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport (χ : M → ℝ))
    (S : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (U : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) (s + 1))
    {d : M → ℝ} (hd : Continuous d) {C_U ε : ℝ} (hε : 0 < ε)
    (hU : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) g x (s + 1) (U x) ≤ C_U * d x) :
    let A := metricNabla0S (I := I) g S
    let B := fun x => (covGradBundleEquiv (I := I) (M := M) 0 s x
      ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
        (unitScalarRSLiftSection (I := I) (M := M) (fun y => S y) x)))
      (unitZeroSec (I := I) (M := M) x)
    let μ := riemannianVolumeMeasure (I := I) (M := M) g
    2 * (∫ x, χ x ^ 2 * inner0S (I := I) g x s
      (covDiv0SField (I := I) g U x) (S x) ∂μ) ≤
      ε * (∫ x, χ x ^ 2 * normSq0S (I := I) g x (s + 1) (A x) ∂μ) +
      (ε⁻¹ + 2) * C_U * (∫ x, χ x ^ 2 * d x ∂μ) +
      2 * (∫ x, normSq0S (I := I) g x (s + 1) (B x) ∂μ) := by
  classical
  dsimp only
  let A := metricNabla0S (I := I) g S
  let B := fun x => (covGradBundleEquiv (I := I) (M := M) 0 s x
      ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
        (unitScalarRSLiftSection (I := I) (M := M) (fun y => S y) x)))
      (unitZeroSec (I := I) (M := M) x)
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  have hi {f : M → ℝ} (hf : Continuous f) : Integrable (fun x => χ x ^ 2 * f x) μ := by
    apply Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g
      ((χ.contMDiff.continuous.pow 2).mul hf)
    apply HasCompactSupport.mono hχ
    intro x hx hzero
    apply hx
    simp [hzero]
  have hAA := hi (normSq0S_cont (I := I) g A)
  have hAUcont : Continuous (fun x => inner0S (I := I) g x (s + 1) (A x) (U x)) := by
    have heq : (fun x => inner0S (I := I) g x (s + 1) (A x) (U x)) =
        fun x => (normSq0S (I := I) g x (s + 1) ((A + U) x) -
          normSq0S (I := I) g x (s + 1) (A x) -
          normSq0S (I := I) g x (s + 1) (U x)) * (1 / 2 : ℝ) := by
      funext x
      change inner0S (I := I) g x (s + 1) (A x) (U x) =
        (normSq0S (I := I) g x (s + 1) (A x + U x) - _ - _) * _
      rw [_root_.Tensor0SBundle.normSq0S_add]
      ring
    rw [heq]
    exact (((normSq0S_cont (I := I) g (A + U)).sub
      (normSq0S_cont (I := I) g A)).sub (normSq0S_cont (I := I) g U)).mul continuous_const
  have hAU := hi hAUcont
  have hdens := hi hd
  obtain ⟨Sc, hSc, hSeq⟩ := (unitScalarRSLiftCₛ (I := I) S).exists_compactly_supported_eq_nhdsSet hχ
  obtain ⟨Uc, hUc, hUeq⟩ := (unitScalarRSLiftCₛ (I := I) U).exists_compactly_supported_eq_nhdsSet hχ
  have hsupport {k : ℕ} (F : Cₛ^∞⟮I; TensorRSModel 0 k ℝ E,
      fun x : M => TensorRSSpace 0 k I x⟯)
      (hF : IsCompact (closure {x : M | F x ≠ 0})) :
      HasCompactSupport (fun x => TensorRSSpace.toModel (F x)) := by
    apply HasCompactSupport.of_support_subset_isCompact hF
    intro x hx
    apply subset_closure
    intro hzero
    exact hx (by simp [hzero, TensorRSSpace.toModel_zero])
  let S₀ : SmoothCcTensor g 0 s := ⟨Sc, hsupport Sc hSc⟩
  let U₀ : SmoothCcTensor g 0 (s + 1) := ⟨Uc, hsupport Uc hUc⟩
  let B₀ := prependCovGradSlot (I := I) g 0 s χ S₀
  have hB (x : M) : B₀.toSection x (unitZeroSec (I := I) x) = B x := by
    rw [show B₀ = prependCovGradSlot (I := I) g 0 s χ S₀ from rfl,
      prependCovGradSlot_toSection_apply]
    by_cases hx : x ∈ tsupport (χ : M → ℝ)
    · have hS : ∀ᶠ y in 𝓝 x, Sc y = unitScalarRSLiftCₛ (I := I) S y :=
        (nhds_le_nhdsSet hx) hSeq
      rw [show S₀.toSection x = unitScalarRSLiftCₛ (I := I) S x from hS.self_of_nhds]
      rfl
    · have hzero : mvfderiv (I := I) (χ : M → ℝ) x = 0 := by
        have hev : (χ : M → ℝ) =ᶠ[𝓝 x] (fun _ => 0) :=
          notMem_tsupport_iff_eventuallyEq.mp hx
        have hmfd_zero : mfderiv I 𝓘(ℝ, ℝ) (χ : M → ℝ) x = 0 := by
          rw [hev.mfderiv_eq]
          exact mfderiv_const
        simp [mvfderiv, hmfd_zero]
      simp only [B, hzero, ContinuousLinearMap.zero_smulRight, map_zero]
  have hBB : Integrable (fun x => normSq0S (I := I) g x (s + 1) (B x)) μ := by
    refine (B₀.integrable_inner_cross B₀).congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [SmoothCcTensor.toFun_apply, innerPt_eq_inner0S, hB, normSq0S_eq_inner]
  have hBU : Integrable (fun x => χ x * inner0S (I := I) g x (s + 1) (B x) (U x)) μ := by
    have hp := (scalarSmul (I := I) g 0 (s + 1) χ B₀).integrable_inner_cross U₀
    refine hp.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [scalarSmul_toFun_apply, tensorInnerPointwise_smul_left]
    by_cases hx : x ∈ tsupport (χ : M → ℝ)
    · have hU : ∀ᶠ y in 𝓝 x, Uc y = unitScalarRSLiftCₛ (I := I) U y :=
        (nhds_le_nhdsSet hx) hUeq
      rw [SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply, innerPt_eq_inner0S, hB,
        show U₀.toSection x = unitScalarRSLiftCₛ (I := I) U x from hU.self_of_nhds,
        unitScalarRSLiftCₛ_apply, unitScalarRSLiftSection_apply_unit]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hpoint (x : M) :
      -(2 * (χ x ^ 2 * inner0S (I := I) g x (s + 1) (A x) (U x))) -
        4 * (χ x * inner0S (I := I) g x (s + 1) (B x) (U x)) ≤
      ε * (χ x ^ 2 * normSq0S (I := I) g x (s + 1) (A x)) +
        ((ε⁻¹ + 2) * C_U) * (χ x ^ 2 * d x) +
        2 * normSq0S (I := I) g x (s + 1) (B x) := by
    by_cases hx : x ∈ tsupport (χ : M → ℝ)
    · have hyoung (D F : Tensor0SSpace (s + 1) I x) {c : ℝ} (hc : 0 < c) :
          -(2 * inner0S (I := I) g x (s + 1) D F) ≤
            c * normSq0S (I := I) g x (s + 1) D +
              c⁻¹ * normSq0S (I := I) g x (s + 1) F := by
        have hp := normSq0S_nonneg (I := I) g x (s + 1) (c • D + F)
        rw [_root_.Tensor0SBundle.normSq0S_add, normSq0S_eq_inner,
          _root_.Tensor0SBundle.inner0S_smul_left,
          _root_.Tensor0SBundle.inner0S_smul_right, ← normSq0S_eq_inner,
          _root_.Tensor0SBundle.inner0S_smul_left] at hp
        have hdiv := div_nonneg hp hc.le
        have heq (a b r : ℝ) : (c * (c * a) + 2 * (c * b) + r) / c =
            c * a + c⁻¹ * r + 2 * b := by
          field_simp
          ring
        rw [heq] at hdiv
        linarith
      have hsmul (c : ℝ) (D : Tensor0SSpace (s + 1) I x) :
          normSq0S (I := I) g x (s + 1) (c • D) =
            c ^ 2 * normSq0S (I := I) g x (s + 1) D := by
        rw [normSq0S_eq_inner, _root_.Tensor0SBundle.inner0S_smul_left,
          _root_.Tensor0SBundle.inner0S_smul_right, ← normSq0S_eq_inner]
        ring
      have hmain := hyoung (χ x • A x) (χ x • U x) hε
      rw [_root_.Tensor0SBundle.inner0S_smul_left,
        _root_.Tensor0SBundle.inner0S_smul_right, hsmul, hsmul] at hmain
      have hboundary := hyoung (B x) (χ x • U x) (c := 1) (by norm_num)
      rw [_root_.Tensor0SBundle.inner0S_smul_right, hsmul] at hboundary
      norm_num only [inv_one, one_mul] at hboundary
      have hbound := mul_le_mul_of_nonneg_left (hU x hx)
        (show 0 ≤ (ε⁻¹ + 2) * χ x ^ 2 by positivity)
      nlinarith only [hmain, hboundary, hbound]
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_pow (by decide : 2 ≠ 0),
        zero_mul, mul_zero, neg_zero, sub_zero, zero_add]
      exact mul_nonneg (by norm_num) (normSq0S_nonneg (I := I) g x (s + 1) (B x))
  have hmono := integral_mono (((hAU.const_mul 2).neg).sub (hBU.const_mul 4))
    (((hAA.const_mul ε).add (hdens.const_mul ((ε⁻¹ + 2) * C_U))).add (hBB.const_mul 2)) hpoint
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply] at hmono
  have hleft := integral_sub ((hAU.const_mul 2).neg) (hBU.const_mul 4)
  have hright := integral_add
    ((hAA.const_mul ε).add (hdens.const_mul ((ε⁻¹ + 2) * C_U))) (hBB.const_mul 2)
  have hright' := integral_add (hAA.const_mul ε) (hdens.const_mul ((ε⁻¹ + 2) * C_U))
  simp only [Pi.neg_apply, Pi.add_apply] at hleft hright hright'
  rw [hleft, hright, hright', integral_neg, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul] at hmono
  have hgreen := integral_sq_weighted_covDiv0SField_eq_neg_metricNabla0S_of_hasCompactSupport
    (I := I) g s χ hχ S U
  change (∫ x, χ x ^ 2 * inner0S (I := I) g x s
      (covDiv0SField (I := I) g U x) (S x) ∂μ) =
    -(∫ x, χ x ^ 2 * inner0S (I := I) g x (s + 1) (A x) (U x) ∂μ) -
      2 * (∫ x, χ x * inner0S (I := I) g x (s + 1) (B x) (U x) ∂μ) at hgreen
  change 2 * (∫ x, χ x ^ 2 * inner0S (I := I) g x s
      (covDiv0SField (I := I) g U x) (S x) ∂μ) ≤
    ε * (∫ x, χ x ^ 2 * normSq0S (I := I) g x (s + 1) (A x) ∂μ) +
      (ε⁻¹ + 2) * C_U * (∫ x, χ x ^ 2 * d x ∂μ) +
      2 * (∫ x, normSq0S (I := I) g x (s + 1) (B x) ∂μ)
  linarith

end DifferentialGeometry.Analysis.Elliptic
