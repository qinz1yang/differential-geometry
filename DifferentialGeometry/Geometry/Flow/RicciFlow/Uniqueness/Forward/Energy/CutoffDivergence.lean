import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.WeightedDivergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.CutoffFlux
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.IntegrationByParts

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Elliptic DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless] [SigmaCompactSpace M]

theorem forward_uniqueness_integral_cutoff_divergence_le
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport (χ : M → ℝ)) (t : ℝ)
    {B₂ BP Background ε : ℝ} (hε : 0 < ε)
    (hB₂ : ∀ x ∈ tsupport (χ : M → ℝ),
      normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ B₂)
    (hBP : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 4
      (CovariantDerivative.riemannCurvature04At (I := I) (g₁ t) (metricCov (I := I) (g₂ t))
        (metricCov_smooth (I := I) (g₂ t)) x) ≤ BP)
    (hBackground : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 2
      (metricTensorField (I := I) (g₂ t) x) ≤ Background) :
    let S := forwardUniquenessSfield (I := I) g₁ g₂ t
    let U := forwardUniquenessUflux (I := I) g₁ g₂ t
    let A := metricNabla0S (I := I) (g₁ t) S
    let B := fun x => (covGradBundleEquiv (I := I) (M := M) 0 4 x
      ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
        (unitScalarRSLiftSection (I := I) (M := M) (fun y => S y) x)))
      (unitZeroSec (I := I) (M := M) x)
    let C_U := 32 * (Module.finrank ℝ E : ℝ) ^ 5 * B₂ +
      8 * (Module.finrank ℝ E : ℝ) ^ 10 * (BP * Background)
    let μ := riemannianVolumeMeasure (I := I) (M := M) (g₁ t)
    2 * (∫ x, χ x ^ 2 * inner0S (I := I) (g₁ t) x 4
      (covDiv0SField (I := I) (g₁ t) U x) (S x) ∂μ) ≤
      ε * (∫ x, χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 (A x) ∂μ) +
      (ε⁻¹ + 2) * C_U * (∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ) +
      2 * (∫ x, normSq0S (I := I) (g₁ t) x 5 (B x) ∂μ) := by
  classical
  dsimp only
  let S := forwardUniquenessSfield (I := I) g₁ g₂ t
  let U := forwardUniquenessUflux (I := I) g₁ g₂ t
  let A := metricNabla0S (I := I) (g₁ t) S
  let B := fun x => (covGradBundleEquiv (I := I) (M := M) 0 4 x
      ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
        (unitScalarRSLiftSection (I := I) (M := M) (fun y => S y) x)))
      (unitZeroSec (I := I) (M := M) x)
  let C_U := 32 * (Module.finrank ℝ E : ℝ) ^ 5 * B₂ +
    8 * (Module.finrank ℝ E : ℝ) ^ 10 * (BP * Background)
  let μ := riemannianVolumeMeasure (I := I) (M := M) (g₁ t)
  have hi {f : M → ℝ} (hf : Continuous f) : Integrable (fun x => χ x ^ 2 * f x) μ := by
    apply Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure (g₁ t)
      ((χ.contMDiff.continuous.pow 2).mul hf)
    apply HasCompactSupport.mono hχ
    intro x hx hzero
    apply hx
    simp [hzero]
  have hAA := hi (normSq0S_continuous (I := I) (g₁ t) A)
  have hAU := hi (inner0S_continuous (I := I) (g₁ t) A U)
  have hdens := hi (dens_continuous (I := I) g₁ g₂ t)
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
  let S₀ : SmoothCcTensor (g₁ t) 0 4 := ⟨Sc, hsupport Sc hSc⟩
  let U₀ : SmoothCcTensor (g₁ t) 0 5 := ⟨Uc, hsupport Uc hUc⟩
  let B₀ := prependCovGradSlot (I := I) (g₁ t) 0 4 χ S₀
  have hB (x : M) : B₀.toSection x (unitZeroSec (I := I) x) = B x := by
    rw [show B₀ = prependCovGradSlot (I := I) (g₁ t) 0 4 χ S₀ from rfl,
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
  have hBB : Integrable (fun x => normSq0S (I := I) (g₁ t) x 5 (B x)) μ := by
    refine (B₀.integrable_inner_cross B₀).congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [SmoothCcTensor.toFun_apply, innerPt_eq_inner0S, hB, normSq0S_eq_inner]
  have hBU : Integrable (fun x => χ x * inner0S (I := I) (g₁ t) x 5 (B x) (U x)) μ := by
    have hp := (scalarSmul (I := I) (g₁ t) 0 5 χ B₀).integrable_inner_cross U₀
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
      -(2 * (χ x ^ 2 * inner0S (I := I) (g₁ t) x 5 (A x) (U x))) -
        4 * (χ x * inner0S (I := I) (g₁ t) x 5 (B x) (U x)) ≤
      ε * (χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 (A x)) +
        ((ε⁻¹ + 2) * C_U) * (χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x) +
        2 * normSq0S (I := I) (g₁ t) x 5 (B x) := by
    by_cases hx : x ∈ tsupport (χ : M → ℝ)
    · have hp := forward_uniqueness_cutoff_flux_le (I := I) g₁ g₂ χ t x hε
        (hB₂ x hx) (hBP x hx) (hBackground x hx)
      dsimp only at hp
      change -(2 * χ x ^ 2 * inner0S (I := I) (g₁ t) x 5 (A x) (U x)) -
        4 * χ x * inner0S (I := I) (g₁ t) x 5 (B x) (U x) ≤
        ε * χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 (A x) +
        (ε⁻¹ + 2) * χ x ^ 2 * C_U * forwardUniqueDensity (I := I) g₁ g₂ t x +
        2 * normSq0S (I := I) (g₁ t) x 5 (B x) at hp
      convert hp using 1 <;> ring
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_pow (by decide : 2 ≠ 0),
        zero_mul, mul_zero, neg_zero, sub_zero, zero_add]
      exact mul_nonneg (by norm_num) (normSq0S_nonneg (I := I) (g₁ t) x 5 (B x))
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
    (I := I) (g₁ t) 4 χ hχ S U
  change (∫ x, χ x ^ 2 * inner0S (I := I) (g₁ t) x 4
      (covDiv0SField (I := I) (g₁ t) U x) (S x) ∂μ) =
    -(∫ x, χ x ^ 2 * inner0S (I := I) (g₁ t) x 5 (A x) (U x) ∂μ) -
      2 * (∫ x, χ x * inner0S (I := I) (g₁ t) x 5 (B x) (U x) ∂μ) at hgreen
  change 2 * (∫ x, χ x ^ 2 * inner0S (I := I) (g₁ t) x 4
      (covDiv0SField (I := I) (g₁ t) U x) (S x) ∂μ) ≤
    ε * (∫ x, χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 (A x) ∂μ) +
      (ε⁻¹ + 2) * C_U * (∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ) +
      2 * (∫ x, normSq0S (I := I) (g₁ t) x 5 (B x) ∂μ)
  linarith

end DifferentialGeometry.PDE.RicciFlow
