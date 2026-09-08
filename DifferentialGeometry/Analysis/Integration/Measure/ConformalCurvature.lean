import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Rellich
import DifferentialGeometry.Analysis.Integration.Measure.Conformal
import DifferentialGeometry.Geometry.Metric.Conformal.Curvature
import DifferentialGeometry.Geometry.Metric.Conformal.LieDerivative
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
import DifferentialGeometry.Geometry.Metric.Conformal.Laplacian
import DifferentialGeometry.Geometry.Metric.Conformal.VectorFieldCurvature

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Integral.Measure

open Bundle MeasureTheory
open DifferentialGeometry.Geometry (IsConformalVectorField isConformalVectorField_conformalMetric_iff)
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [I.Boundaryless] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem integral_laplacian_mul_divergence_eq_integral_scalarCurv_mul_action
    (g : SmoothRiemannianMetric I M) (hn : Module.finrank Real E = 2)
    (u : C^∞⟮I, M; Real⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : IsConformalVectorField g X) :
    (∫ x, ΔG g u x * divergenceG g X x ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, scalarCurv g x * tangentSectionAction X u x
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let d : C^∞⟮I, M; Real⟯ := ⟨divergenceG g X, divergence_g_contMDiff g X⟩
  let R : C^∞⟮I, M; Real⟯ := ⟨scalarCurv g, scalarCurv_contMDiff g⟩
  let a := tangentSectionAction X u
  let L := ΔG g u
  let b := tangentSectionAction X R
  have hi {f : M → Real} (hf : Continuous f) : Integrable f μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g hf
      (HasCompactSupport.of_compactSpace f)
  have ha : Continuous a := (tangentSectionAction_contMDiff X u.contMDiff).continuous
  have hL : Continuous L := (Δ_g_contMDiff g u).continuous
  have hb : Continuous b := (tangentSectionAction_contMDiff X R.contMDiff).continuous
  have hP := integral_tangentSectionAction_mul_add_eq_neg g R.contMDiff u.contMDiff X
    (HasCompactSupport.of_compactSpace X)
  change (∫ x, b x * u x + R x * a x ∂μ) = -∫ x, R x * u x * d x ∂μ at hP
  have hPadd := integral_add (hi (hb.mul u.contMDiff.continuous)) (hi (R.contMDiff.continuous.mul ha))
  simp only [Pi.mul_apply] at hPadd
  rw [hPadd] at hP
  have hgreen := green_second_integral_smul_laplacian_sub_eq_zero g u.contMDiff d.contMDiff
  change (∫ x, u x * ΔG g d x - d x * L x ∂μ) = 0 at hgreen
  have hde (x : M) : ΔG g d x = -(R x * d x) - b x := by
    have h := IsConformalVectorField.laplacian_divergence_add_scalarCurv_mul_divergence_of_finrank_eq_two g hn X hX x
    change ΔG g d x + R x * d x = -b x at h
    linarith
  have hgreen_rewrite : (∫ x, u x * ΔG g d x - d x * L x ∂μ) =
      -(∫ x, R x * u x * d x ∂μ) - (∫ x, b x * u x ∂μ) - ∫ x, L x * d x ∂μ := by
    calc
      _ = ∫ x, -(R x * u x * d x) - b x * u x - L x * d x ∂μ := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun x => ?_
        dsimp only
        rw [hde]
        ring
      _ = _ := by
        have h₁ := integral_sub ((hi ((R.contMDiff.continuous.mul u.contMDiff.continuous).mul d.contMDiff.continuous)).neg.sub
          (hi (hb.mul u.contMDiff.continuous))) (hi (hL.mul d.contMDiff.continuous))
        have h₂ := integral_sub (hi ((R.contMDiff.continuous.mul u.contMDiff.continuous).mul d.contMDiff.continuous)).neg
          (hi (hb.mul u.contMDiff.continuous))
        simp only [Pi.mul_apply, Pi.sub_apply, Pi.neg_apply] at h₁ h₂
        rw [h₁, h₂, integral_neg]
  rw [hgreen_rewrite] at hgreen
  have hbalance : (∫ x, L x * d x ∂μ) = ∫ x, R x * a x ∂μ := by linarith
  exact hbalance

private theorem integral_scalarCurv_mul_divergence_conformalMetric
    (g : SmoothRiemannianMetric I M) (hn : Module.finrank Real E = 2)
    (u : C^∞⟮I, M; Real⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (∫ x, Real.exp (2 * u x) *
      (scalarCurv (conformalMetric g u) x * divergenceG (conformalMetric g u) X x)
      ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      (∫ x, scalarCurv g x * divergenceG g X x ∂riemannianVolumeMeasure (I := I) (M := M) g) +
      2 * (∫ x, scalarCurv g x * tangentSectionAction X u x ∂riemannianVolumeMeasure (I := I) (M := M) g) -
      2 * (∫ x, ΔG g u x * divergenceG g X x ∂riemannianVolumeMeasure (I := I) (M := M) g) -
      4 * ∫ x, ΔG g u x * tangentSectionAction X u x ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let d : C^∞⟮I, M; Real⟯ := ⟨divergenceG g X, divergence_g_contMDiff g X⟩
  let R : C^∞⟮I, M; Real⟯ := ⟨scalarCurv g, scalarCurv_contMDiff g⟩
  let a := tangentSectionAction X u
  let L := ΔG g u
  have hi {f : M → Real} (hf : Continuous f) : Integrable f μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g hf
      (HasCompactSupport.of_compactSpace f)
  have ha : Continuous a := (tangentSectionAction_contMDiff X u.contMDiff).continuous
  have hL : Continuous L := (Δ_g_contMDiff g u).continuous
  have hdiv (x : M) : divergenceG (conformalMetric g u) X x = d x + 2 * a x := by
    have h := divergence_conformalMetric g u (X := (X : (y : M) → TangentSpace I y)) (x := x) X.mdifferentiableAt
    change divergence (LeviCivita (conformalMetric g u)) X.toFun x =
      divergence (LeviCivita g) X.toFun x + (Module.finrank Real E : Real) *
        mvfderiv I (u : M → Real) x (X x) at h
    rw [divergence_levi_eq (conformalMetric g u) X x, divergence_levi_eq g X x, hn] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hRu (x : M) : scalarCurv (conformalMetric g u) x * Real.exp (2 * u x) = R x - 2 * L x := by
    rw [scalarCurv_conformalMetric_of_finrank_eq_two g u hn, laplacian_levi_eq g u.contMDiff x]
    have hu : (⟨(u : M → Real), u.contMDiff⟩ : C^∞⟮I, M; Real⟯) = u := rfl
    rw [hu]
    have hexp : Real.exp (-(2 * u x)) * Real.exp (2 * u x) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    change Real.exp (-(2 * u x)) * (R x - 2 * L x) * Real.exp (2 * u x) = _
    rw [mul_right_comm, hexp, one_mul]
  have heq : (∫ x, Real.exp (2 * u x) *
      (scalarCurv (conformalMetric g u) x * divergenceG (conformalMetric g u) X x) ∂μ) =
      (∫ x, R x * d x ∂μ) + 2 * (∫ x, R x * a x ∂μ) -
        2 * (∫ x, L x * d x ∂μ) - 4 * ∫ x, L x * a x ∂μ := by
    calc
      _ = ∫ x, R x * d x + 2 * (R x * a x) - 2 * (L x * d x) - 4 * (L x * a x) ∂μ := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun x => ?_
        dsimp only
        rw [hdiv]
        calc
          _ = (scalarCurv (conformalMetric g u) x * Real.exp (2 * u x)) * (d x + 2 * a x) := by ring
          _ = _ := by rw [hRu]; ring
      _ = _ := by
        have h₁ := integral_sub (((hi (R.contMDiff.continuous.mul d.contMDiff.continuous)).add
          ((hi (R.contMDiff.continuous.mul ha)).const_mul 2)).sub
          ((hi (hL.mul d.contMDiff.continuous)).const_mul 2)) ((hi (hL.mul ha)).const_mul 4)
        have h₂ := integral_sub ((hi (R.contMDiff.continuous.mul d.contMDiff.continuous)).add
          ((hi (R.contMDiff.continuous.mul ha)).const_mul 2)) ((hi (hL.mul d.contMDiff.continuous)).const_mul 2)
        have h₃ := integral_add (hi (R.contMDiff.continuous.mul d.contMDiff.continuous))
          ((hi (R.contMDiff.continuous.mul ha)).const_mul 2)
        simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply] at h₁ h₂ h₃
        rw [h₁, h₂, h₃, integral_const_mul, integral_const_mul, integral_const_mul]
  exact heq

theorem integral_inner_gradientFun_scalarCurv_conformalMetric
    (g : SmoothRiemannianMetric I M) (hn : Module.finrank Real E = 2)
    (u : C^∞⟮I, M; Real⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : IsConformalVectorField g X) :
    (∫ x, (conformalMetric g u).inner x
      (gradientFun (conformalMetric g u) (scalarCurv (conformalMetric g u)) x) (X x)
      ∂riemannianVolumeMeasure (I := I) (M := M) (conformalMetric g u)) =
      ∫ x, g.inner x (gradientFun g (scalarCurv g) x) (X x)
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let d : C^∞⟮I, M; Real⟯ := ⟨divergenceG g X, divergence_g_contMDiff g X⟩
  let R : C^∞⟮I, M; Real⟯ := ⟨scalarCurv g, scalarCurv_contMDiff g⟩
  let a := tangentSectionAction X u
  let L := ΔG g u
  have hbalance : (∫ x, L x * d x ∂μ) = ∫ x, R x * a x ∂μ :=
    integral_laplacian_mul_divergence_eq_integral_scalarCurv_mul_action g hn u X hX
  have hLa : (∫ x, L x * a x ∂μ) = 0 :=
    integral_laplacian_mul_tangentSectionAction_eq_zero_of_conformal_of_finrank_eq_two hn g u X hX
  have hIBP := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (conformalMetric g u) (scalarCurv_contMDiff (conformalMetric g u)) X
    (HasCompactSupport.of_compactSpace X)
  have hIBPg := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    g R.contMDiff X (HasCompactSupport.of_compactSpace X)
  simp_rw [inner_gradientFun]
  change (∫ x, tangentSectionAction X (scalarCurv (conformalMetric g u)) x
    ∂riemannianVolumeMeasure (I := I) (M := M) (conformalMetric g u)) = ∫ x, tangentSectionAction X R x ∂μ
  rw [hIBP, hIBPg, integral_conformalMetric_eq_integral_smul_exp]
  simp only [hn, Nat.cast_ofNat, smul_eq_mul]
  apply congrArg Neg.neg
  have heq := integral_scalarCurv_mul_divergence_conformalMetric g hn u X
  change (∫ x, Real.exp (2 * u x) *
      (scalarCurv (conformalMetric g u) x * divergenceG (conformalMetric g u) X x) ∂μ) =
      (∫ x, R x * d x ∂μ) + 2 * (∫ x, R x * a x ∂μ) -
        2 * (∫ x, L x * d x ∂μ) - 4 * ∫ x, L x * a x ∂μ at heq
  rw [heq, hbalance, hLa]
  simp only [mul_zero, sub_zero, add_sub_cancel_right]
  rfl

theorem integral_inner_gradientFun_scalarCurv_conformalMetric_eq_zero_of_constant_scalarCurv
    (g : SmoothRiemannianMetric I M) (hn : Module.finrank Real E = 2)
    (u : C^∞⟮I, M; Real⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : IsConformalVectorField (conformalMetric g u) X) {R : Real}
    (hR : ∀ y, scalarCurv g y = R) :
    (∫ x, (conformalMetric g u).inner x
      (gradientFun (conformalMetric g u) (scalarCurv (conformalMetric g u)) x) (X x)
      ∂riemannianVolumeMeasure (I := I) (M := M) (conformalMetric g u)) = 0 := by
  rw [integral_inner_gradientFun_scalarCurv_conformalMetric g hn u X
    ((isConformalVectorField_conformalMetric_iff g u X).mp hX)]
  have hf : scalarCurv g = fun _ => R := funext hR
  simp_rw [inner_gradientFun, hf, mvfderiv_const, zero_apply]
  exact integral_zero _ _

end DifferentialGeometry.Integral.Measure
