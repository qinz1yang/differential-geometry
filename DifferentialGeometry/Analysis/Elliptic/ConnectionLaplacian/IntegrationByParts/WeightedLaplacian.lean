import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.WeightedDivergence
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.IntegrationByParts
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

noncomputable section

namespace DifferentialGeometry.Analysis.Elliptic

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.PDE.RicciFlow
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless] [SigmaCompactSpace M]

theorem integral_sq_weighted_roughLap0SField_le_of_hasCompactSupport
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport (χ : M → ℝ))
    (S : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    {η : ℝ} (hη : 0 < η) :
    let A := metricNabla0S (I := I) g S
    let B := fun x => (covGradBundleEquiv (I := I) (M := M) 0 s x
      ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
        (unitScalarRSLiftSection (I := I) (M := M) (fun y => S y) x)))
      (unitZeroSec (I := I) (M := M) x)
    let μ := riemannianVolumeMeasure (I := I) (M := M) g
    (∫ x, χ x ^ 2 * inner0S (I := I) g x s
      (roughLap0SField (I := I) g S x) (S x) ∂μ) ≤
      (η - 1) * (∫ x, χ x ^ 2 * normSq0S (I := I) g x (s + 1) (A x) ∂μ) +
      η⁻¹ * (∫ x, normSq0S (I := I) g x (s + 1) (B x) ∂μ) := by
  classical
  dsimp only
  let A := metricNabla0S (I := I) g S
  let B := fun x => (covGradBundleEquiv (I := I) (M := M) 0 s x
      ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
        (unitScalarRSLiftSection (I := I) (M := M) (fun y => S y) x)))
      (unitZeroSec (I := I) (M := M) x)
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  obtain ⟨Sc, hSc, hSeq⟩ := (unitScalarRSLiftCₛ (I := I) S).exists_compactly_supported_eq_nhdsSet hχ
  obtain ⟨Ac, hAc, hAeq⟩ := (unitScalarRSLiftCₛ (I := I) A).exists_compactly_supported_eq_nhdsSet hχ
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
  let A₀ : SmoothCcTensor g 0 (s + 1) := ⟨Ac, hsupport Ac hAc⟩
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
  have hBA : Integrable (fun x => χ x * inner0S (I := I) g x (s + 1) (B x) (A x)) μ := by
    have hp := (scalarSmul (I := I) g 0 (s + 1) χ B₀).integrable_inner_cross A₀
    refine hp.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [scalarSmul_toFun_apply, tensorInnerPointwise_smul_left]
    by_cases hx : x ∈ tsupport (χ : M → ℝ)
    · have hA : ∀ᶠ y in 𝓝 x, Ac y = unitScalarRSLiftCₛ (I := I) A y :=
        (nhds_le_nhdsSet hx) hAeq
      rw [SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply, innerPt_eq_inner0S, hB,
        show A₀.toSection x = unitScalarRSLiftCₛ (I := I) A x from hA.self_of_nhds,
        unitScalarRSLiftCₛ_apply, unitScalarRSLiftSection_apply_unit]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hAA : Integrable (fun x => χ x ^ 2 * normSq0S (I := I) g x (s + 1) (A x)) μ := by
    let V := scalarSmul (I := I) g 0 (s + 1) χ A₀
    refine (V.integrable_inner_cross V).congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only [V]
    rw [scalarSmul_toFun_apply, tensorInnerPointwise_smul_left,
      tensorInnerPointwise_smul_right]
    by_cases hx : x ∈ tsupport (χ : M → ℝ)
    · have hA : ∀ᶠ y in 𝓝 x, Ac y = unitScalarRSLiftCₛ (I := I) A y :=
        (nhds_le_nhdsSet hx) hAeq
      rw [SmoothCcTensor.toFun_apply, innerPt_eq_inner0S,
        show A₀.toSection x = unitScalarRSLiftCₛ (I := I) A x from hA.self_of_nhds,
        unitScalarRSLiftCₛ_apply, unitScalarRSLiftSection_apply_unit, normSq0S_eq_inner]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hpoint (x : M) :
      -(2 * (χ x * inner0S (I := I) g x (s + 1) (B x) (A x))) ≤
        η * (χ x ^ 2 * normSq0S (I := I) g x (s + 1) (A x)) +
          η⁻¹ * normSq0S (I := I) g x (s + 1) (B x) := by
    have hp := normSq0S_nonneg (I := I) g x (s + 1) ((η * χ x) • A x + B x)
    rw [_root_.Tensor0SBundle.normSq0S_add,
      normSq0S_eq_inner,
      _root_.Tensor0SBundle.inner0S_smul_left,
      _root_.Tensor0SBundle.inner0S_smul_right,
      ← normSq0S_eq_inner,
      _root_.Tensor0SBundle.inner0S_smul_left,
      _root_.Tensor0SBundle.inner0S_comm g x (s + 1) (A x) (B x)] at hp
    have hdiv := div_nonneg hp hη.le
    have halgebra (a b c : ℝ) :
        ((η * χ x) * ((η * χ x) * a) + 2 * ((η * χ x) * b) + c) / η =
          η * (χ x ^ 2 * a) + η⁻¹ * c + 2 * (χ x * b) := by
      field_simp
      ring
    rw [halgebra] at hdiv
    linarith
  have hi := integral_mono ((hBA.const_mul 2).neg)
    ((hAA.const_mul η).add (hBB.const_mul η⁻¹)) hpoint
  simp only [Pi.neg_apply, Pi.add_apply] at hi
  rw [integral_neg, integral_const_mul,
    integral_add (hAA.const_mul η) (hBB.const_mul η⁻¹),
    integral_const_mul, integral_const_mul] at hi
  have hg := integral_sq_weighted_covDiv0SField_eq_neg_metricNabla0S_of_hasCompactSupport
    (I := I) g s χ hχ S A
  change (∫ x, χ x ^ 2 * inner0S (I := I) g x s
      (roughLap0SField (I := I) g S x) (S x) ∂μ) =
    -(∫ x, χ x ^ 2 * normSq0S (I := I) g x (s + 1) (A x) ∂μ) -
      2 * (∫ x, χ x * inner0S (I := I) g x (s + 1) (B x) (A x) ∂μ) at hg
  change (∫ x, χ x ^ 2 * inner0S (I := I) g x s
      (roughLap0SField (I := I) g S x) (S x) ∂μ) ≤
    (η - 1) * (∫ x, χ x ^ 2 * normSq0S (I := I) g x (s + 1) (A x) ∂μ) +
      η⁻¹ * (∫ x, normSq0S (I := I) g x (s + 1) (B x) ∂μ)
  linarith

end DifferentialGeometry.Analysis.Elliptic
