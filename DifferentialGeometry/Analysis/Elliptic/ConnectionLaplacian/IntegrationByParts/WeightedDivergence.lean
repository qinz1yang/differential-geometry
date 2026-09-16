import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.Divergence
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRS.Pairing
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Tensor0SRSCovariantDerivativeAgreement
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Nabla0SFunAgreement
import DifferentialGeometry.Geometry.Operator.CovariantTensor
import DifferentialGeometry.Geometry.Operator.MetricTraceOrthonormalFrame
import DifferentialGeometry.Analysis.Calculus.CompactSupportSection

noncomputable section
set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Elliptic

open Bundle Manifold MeasureTheory Set Filter
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.TensorRSNabla DifferentialGeometry.PDE.RicciFlow
open scoped Manifold Topology ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

private theorem covariant_derivative_lift_unit (g : SmoothRiemannianMetric I M)
    {s : ℕ} (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (x : M) (v : TangentSpace I x) (slots : Fin s → TangentSpace I x) :
    (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
      (fun y => unitScalarRSLiftCₛ (I := I) T y) x v)
      (unitZeroSec (I := I) x) slots =
        metricNabla0S (I := I) g T x (Fin.cons v slots) := by
  rw [← tensor0SCovariantDerivative_eq_tensorRSCovariantDerivative (I := I) g s T x v]
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v
  subst hX
  rw [← nabla0SFun_eq_tensor0SCovariantDerivative (I := I) g s X T x]
  exact (totalNabla0SFun_apply_section (I := I) s (LeviCivita (I := I) g)
    X T x slots).symm

private theorem covariant_derivative_unit_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (Tc : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, fun y : M => TensorRSSpace 0 s I y⟯)
    {x : M} (h : ∀ᶠ y in 𝓝 x, Tc y = unitScalarRSLiftCₛ (I := I) T y)
    (v : TangentSpace I x) (slots : Fin s → TangentSpace I x) :
    (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g) Tc x v)
      (unitZeroSec (I := I) x) slots =
        metricNabla0S (I := I) g T x (Fin.cons v slots) := by
  rw [tensorRSCovariantDerivative_congr_of_eventuallyEq (I := I) g 0 s h
    (Tc.contMDiff.mdifferentiableAt (by simp))
    ((unitScalarRSLiftCₛ (I := I) T).contMDiff.mdifferentiableAt (by simp))]
  exact covariant_derivative_lift_unit g T x v slots

variable [I.Boundaryless]

private theorem covGrad_unit_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (Tc : SmoothCcTensor g 0 s)
    {x : M} (h : ∀ᶠ y in 𝓝 x, Tc.toSection y = unitScalarRSLiftCₛ (I := I) T y) :
    (covGrad (I := I) g 0 s Tc).toSection x (unitZeroSec (I := I) x) =
      metricNabla0S (I := I) g T x := by
  apply tensor0SSpace_ext
  intro slots
  rw [covGrad_toSection_apply]
  change Tensor0SSpace.eval
    ((covGradBundleEquiv (I := I) 0 s x
      (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g) Tc.toSection x))
      (unitZeroSec (I := I) x)) slots = _
  rw [covGradBundleEquiv_apply_eval]
  have hv := covariant_derivative_unit_of_eventuallyEq g T Tc.toSection h
    (slots 0) (Matrix.vecTail slots)
  change (((tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
    Tc.toSection x) (slots 0)) (unitZeroSec (I := I) x)) (Matrix.vecTail slots) = _
  rw [hv]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Matrix.vecTail]

variable [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
private theorem covDivergence_unit_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (V : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) (s + 1))
    (Vc : SmoothCcTensor g 0 (s + 1))
    {x : M} (h : ∀ᶠ y in 𝓝 x, Vc.toSection y = unitScalarRSLiftCₛ (I := I) V y) :
    (covDivergence (I := I) g s Vc).toSection x (unitZeroSec (I := I) x) =
      covDiv0SField (I := I) g V x := by
  classical
  apply tensor0SSpace_ext
  intro slots
  rw [covDiv0SField, metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_smoothOrthoFrame]
  change ((∑ i : Fin (Module.finrank ℝ E),
    covDivergenceBilinear (I := I) g s Vc x
      (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x))
      (unitZeroSec (I := I) x)) slots = _
  rw [sum_apply, Tensor0SSpace.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hsmooth := (smoothOrthoFrame_smooth (I := I) g x i).contMDiffAt.mdifferentiableAt (x := x)
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  rw [codiffPsi_apply (I := I) g s Vc x hsmooth hsmooth]
  exact covariant_derivative_unit_of_eventuallyEq g V Vc.toSection h
    (smoothOrthoFrame (I := I) g x i x)
    (Fin.cons (smoothOrthoFrame (I := I) g x i x) slots)

private theorem integral_weighted_covDivergence_eq_neg_covGrad
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (χ : C^∞⟮I, M; ℝ⟯) (T : SmoothCcTensor g 0 s) (V : SmoothCcTensor g 0 (s + 1)) :
    (∫ x, χ x * tensorInnerPointwise (I := I) g 0 s x
      ((covDivergence (I := I) g s V).toFun x) (T.toFun x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      -(∫ x, χ x * tensorInnerPointwise (I := I) g 0 (s + 1) x
        ((covGrad (I := I) g 0 s T).toFun x) (V.toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
      ∫ x, tensorInnerPointwise (I := I) g 0 (s + 1) x
        ((prependCovGradSlot (I := I) g 0 s χ T).toFun x) (V.toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let A := covGrad (I := I) g 0 s (scalarSmul (I := I) g 0 s χ T)
  let B := scalarSmul (I := I) g 0 (s + 1) χ (covGrad (I := I) g 0 s T)
  let C := prependCovGradSlot (I := I) g 0 s χ T
  have hA : A = B + C := by
    change A = B + (A - B)
    abel
  have hsplit : ∀ x, tensorInnerPointwise (I := I) g 0 (s + 1) x (A.toFun x) (V.toFun x) =
      χ x * tensorInnerPointwise (I := I) g 0 (s + 1) x
        ((covGrad (I := I) g 0 s T).toFun x) (V.toFun x) +
      tensorInnerPointwise (I := I) g 0 (s + 1) x (C.toFun x) (V.toFun x) := by
    intro x
    rw [hA]
    change tensorInnerPointwise (I := I) g 0 (s + 1) x
      (TensorRSSpace.toModel (B.toSection x + C.toSection x)) _ = _
    rw [TensorRSSpace.toModel_add, tensorInnerPointwise_add_left,
      show TensorRSSpace.toModel (B.toSection x) = B.toFun x from rfl,
      show B = scalarSmul (I := I) g 0 (s + 1) χ (covGrad (I := I) g 0 s T) from rfl,
      scalarSmul_toFun_apply, tensorInnerPointwise_smul_left]
    rfl
  have hi := B.integrable_inner_cross V
  have hi' : Integrable (fun x => χ x * tensorInnerPointwise (I := I) g 0 (s + 1) x
      ((covGrad (I := I) g 0 s T).toFun x) (V.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine hi.congr (Filter.Eventually.of_forall (fun x => ?_))
    dsimp only
    rw [show B = scalarSmul (I := I) g 0 (s + 1) χ (covGrad (I := I) g 0 s T) from rfl,
      scalarSmul_toFun_apply, tensorInnerPointwise_smul_left]
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence (I := I) g s
    (scalarSmul (I := I) g 0 s χ T) V
  change (∫ x, tensorInnerPointwise (I := I) g 0 (s + 1) x (A.toFun x) (V.toFun x)
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = _ at hgreen
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
    integral_add hi' (C.integrable_inner_cross V), tensorL2Inner] at hgreen
  have hpull : ∀ x, tensorInnerPointwise (I := I) g 0 s x
      ((scalarSmul (I := I) g 0 s χ T).toFun x)
      ((covDivergence (I := I) g s V).toFun x) =
      χ x * tensorInnerPointwise (I := I) g 0 s x
        ((covDivergence (I := I) g s V).toFun x) (T.toFun x) := by
    intro x
    rw [scalarSmul_toFun_apply, tensorInnerPointwise_smul_left,
      tensorInnerPointwise_symm]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpull)] at hgreen
  linarith


omit [BoundarylessManifold I M] in
theorem integral_weighted_covDiv0SField_eq_neg_metricNabla0S_of_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport (χ : M → ℝ))
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (V : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) (s + 1)) :
    let dχT := fun x => (covGradBundleEquiv (I := I) (M := M) 0 s x
      ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
        (unitScalarRSLiftSection (I := I) (M := M) (fun y => T y) x)))
      (unitZeroSec (I := I) x)
    (∫ x, χ x * inner0S (I := I) g x s (covDiv0SField (I := I) g V x) (T x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      -(∫ x, χ x * inner0S (I := I) g x (s + 1) (metricNabla0S (I := I) g T x) (V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
      ∫ x, inner0S (I := I) g x (s + 1) (dχT x) (V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  dsimp only
  obtain ⟨Tc, hTc, hTeq⟩ := (unitScalarRSLiftCₛ (I := I) T).exists_compactly_supported_eq_nhdsSet hχ
  obtain ⟨Vc, hVc, hVeq⟩ := (unitScalarRSLiftCₛ (I := I) V).exists_compactly_supported_eq_nhdsSet hχ
  have hsupport {k : ℕ} (S : Cₛ^∞⟮I; TensorRSModel 0 k ℝ E,
      (fun x : M => TensorRSSpace 0 k I x)⟯)
      (hS : IsCompact (closure {x : M | S x ≠ 0})) :
      HasCompactSupport (fun x => TensorRSSpace.toModel (S x)) := by
    apply HasCompactSupport.of_support_subset_isCompact hS
    intro x hx
    apply subset_closure
    intro hzero
    exact hx (by simp [hzero, TensorRSSpace.toModel_zero])
  let T₀ : SmoothCcTensor g 0 s := ⟨Tc, hsupport Tc hTc⟩
  let V₀ : SmoothCcTensor g 0 (s + 1) := ⟨Vc, hsupport Vc hVc⟩
  have hdiv : ∀ x, χ x * tensorInnerPointwise (I := I) g 0 s x
      ((covDivergence (I := I) g s V₀).toFun x) (T₀.toFun x) =
      χ x * inner0S (I := I) g x s (covDiv0SField (I := I) g V x) (T x) := by
    intro x
    by_cases hx : x ∈ tsupport (χ : M → ℝ)
    · have hT : ∀ᶠ y in 𝓝 x, Tc y = unitScalarRSLiftCₛ (I := I) T y :=
        (nhds_le_nhdsSet hx) hTeq
      have hV : ∀ᶠ y in 𝓝 x, Vc y = unitScalarRSLiftCₛ (I := I) V y :=
        (nhds_le_nhdsSet hx) hVeq
      rw [SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply,
        innerPt_eq_inner0S, covDivergence_unit_of_eventuallyEq g V V₀ hV]
      rw [show T₀.toSection x = unitScalarRSLiftCₛ (I := I) T x from hT.self_of_nhds,
        unitScalarRSLiftCₛ_apply, unitScalarRSLiftSection_apply_unit]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hgrad : ∀ x, χ x * tensorInnerPointwise (I := I) g 0 (s + 1) x
      ((covGrad (I := I) g 0 s T₀).toFun x) (V₀.toFun x) =
      χ x * inner0S (I := I) g x (s + 1) (metricNabla0S (I := I) g T x) (V x) := by
    intro x
    by_cases hx : x ∈ tsupport (χ : M → ℝ)
    · have hT : ∀ᶠ y in 𝓝 x, Tc y = unitScalarRSLiftCₛ (I := I) T y :=
        (nhds_le_nhdsSet hx) hTeq
      have hV : ∀ᶠ y in 𝓝 x, Vc y = unitScalarRSLiftCₛ (I := I) V y :=
        (nhds_le_nhdsSet hx) hVeq
      rw [SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply,
        innerPt_eq_inner0S, covGrad_unit_of_eventuallyEq g T T₀ hT]
      rw [show V₀.toSection x = unitScalarRSLiftCₛ (I := I) V x from hV.self_of_nhds,
        unitScalarRSLiftCₛ_apply, unitScalarRSLiftSection_apply_unit]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hcross : ∀ x, tensorInnerPointwise (I := I) g 0 (s + 1) x
      ((prependCovGradSlot (I := I) g 0 s χ T₀).toFun x) (V₀.toFun x) =
      inner0S (I := I) g x (s + 1)
        ((covGradBundleEquiv (I := I) (M := M) 0 s x
          ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
            (unitScalarRSLiftSection (I := I) (M := M) (fun y => T y) x)))
          (unitZeroSec (I := I) x)) (V x) := by
    intro x
    rw [SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply,
      innerPt_eq_inner0S, prependCovGradSlot_toSection_apply]
    by_cases hx : x ∈ tsupport (χ : M → ℝ)
    · have hT : ∀ᶠ y in 𝓝 x, Tc y = unitScalarRSLiftCₛ (I := I) T y :=
        (nhds_le_nhdsSet hx) hTeq
      have hV : ∀ᶠ y in 𝓝 x, Vc y = unitScalarRSLiftCₛ (I := I) V y :=
        (nhds_le_nhdsSet hx) hVeq
      rw [show T₀.toSection x = unitScalarRSLiftCₛ (I := I) T x from hT.self_of_nhds,
        show V₀.toSection x = unitScalarRSLiftCₛ (I := I) V x from hV.self_of_nhds,
        unitScalarRSLiftCₛ_apply, unitScalarRSLiftCₛ_apply,
        unitScalarRSLiftSection_apply_unit]
    · have hzero : mvfderiv (I := I) (χ : M → ℝ) x = 0 := by
        have hev : (χ : M → ℝ) =ᶠ[𝓝 x] (fun _ => 0) :=
          notMem_tsupport_iff_eventuallyEq.mp hx
        have hmfd_zero : mfderiv I 𝓘(ℝ, ℝ) (χ : M → ℝ) x = 0 := by
          rw [hev.mfderiv_eq]
          exact mfderiv_const
        simp [mvfderiv, hmfd_zero]
      have hz (W : Tensor0SSpace (s + 1) I x) : inner0S (I := I) g x (s + 1) 0 W = 0 := by
        have hh := _root_.Tensor0SBundle.inner0S_smul_left (I := I) g x (s + 1)
          (0 : ℝ) (0 : Tensor0SSpace (s + 1) I x) W
        simpa only [zero_smul, zero_mul] using hh
      simp only [hzero, ContinuousLinearMap.zero_smulRight, map_zero,
        TensorRSSpace.zero_apply, hz]
  have hgreen := integral_weighted_covDivergence_eq_neg_covGrad g s χ T₀ V₀
  rw [integral_congr_ae (Filter.Eventually.of_forall hdiv),
    integral_congr_ae (Filter.Eventually.of_forall hgrad),
    integral_congr_ae (Filter.Eventually.of_forall hcross)] at hgreen
  exact hgreen


omit [BoundarylessManifold I M] in
theorem integral_sq_weighted_covDiv0SField_eq_neg_metricNabla0S_of_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport (χ : M → ℝ))
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (V : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) (s + 1)) :
    let dχT := fun x => (covGradBundleEquiv (I := I) (M := M) 0 s x
      ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
        (unitScalarRSLiftSection (I := I) (M := M) (fun y => T y) x)))
      (unitZeroSec (I := I) x)
    (∫ x, χ x ^ 2 * inner0S (I := I) g x s (covDiv0SField (I := I) g V x) (T x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      -(∫ x, χ x ^ 2 * inner0S (I := I) g x (s + 1) (metricNabla0S (I := I) g T x) (V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
      2 * ∫ x, χ x * inner0S (I := I) g x (s + 1) (dχT x) (V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  dsimp only
  have hder (x : M) : mvfderiv (I := I) ((χ * χ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x =
      (2 * χ x) • mvfderiv (I := I) (χ : M → ℝ) x := by
    ext v
    change mvfderiv (I := I) (fun y => χ y * χ y) x v = _
    rw [DifferentialGeometry.mvfderiv_mul_at v
      (χ.contMDiff.mdifferentiableAt (by simp)) (χ.contMDiff.mdifferentiableAt (by simp)),
      smul_apply]
    change χ x * _ + χ x * _ = (2 * χ x) * _
    ring
  have hcross (x : M) :
      inner0S (I := I) g x (s + 1)
        ((covGradBundleEquiv (I := I) (M := M) 0 s x
          ((mvfderiv (I := I) ((χ * χ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x).smulRight
            (unitScalarRSLiftSection (I := I) (M := M) (fun y => T y) x)))
          (unitZeroSec (I := I) x)) (V x) =
        2 * (χ x * inner0S (I := I) g x (s + 1)
          ((covGradBundleEquiv (I := I) (M := M) 0 s x
            ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
              (unitScalarRSLiftSection (I := I) (M := M) (fun y => T y) x)))
            (unitZeroSec (I := I) x)) (V x)) := by
    rw [hder]
    have hs : ((2 * χ x) • mvfderiv (I := I) (χ : M → ℝ) x).smulRight
        (unitScalarRSLiftSection (I := I) (M := M) (fun y => T y) x) =
        (2 * χ x) • (mvfderiv (I := I) (χ : M → ℝ) x).smulRight
          (unitScalarRSLiftSection (I := I) (M := M) (fun y => T y) x) := by
      ext v
      simp only [ContinuousLinearMap.smulRight_apply, smul_apply,
        smul_smul, smul_eq_mul]
    rw [hs, map_smul, TensorRSSpace.smul_apply, _root_.Tensor0SBundle.inner0S_smul_left]
    ring
  have hgreen := integral_weighted_covDiv0SField_eq_neg_metricNabla0S_of_hasCompactSupport
    g s (χ * χ) hχ.mul_right T V
  dsimp only at hgreen
  rw [integral_congr_ae (Filter.Eventually.of_forall hcross), integral_const_mul] at hgreen
  simpa only [pow_two, ContMDiffMap.coe_mul, Pi.mul_apply] using hgreen

end DifferentialGeometry.Analysis.Elliptic
