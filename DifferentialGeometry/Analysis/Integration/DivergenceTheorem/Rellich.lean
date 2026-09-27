import DifferentialGeometry.Geometry.Metric.Conformal.VectorField
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Identities

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Integral.DivergenceTheorem

open Bundle MeasureTheory
open Geometry.Operator
open Geometry.Connection (LeviCivita)
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem rellich_identity (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    2 * (∫ x, ΔG g u x * tangentSectionAction X u x ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      (∫ x, normGradSqFun g u x * divergenceG g X x ∂riemannianVolumeMeasure (I := I) (M := M) g) -
        2 * (∫ x, g.inner x ((LeviCivita g) X x (gradG g u x)) (gradG g u x)
          ∂riemannianVolumeMeasure (I := I) (M := M) g) := by
  let U := gradG g u
  let α := tangentSectionAction X u
  let S := normGradSqFun g u
  let A := fun x => g.inner x ((LeviCivita g) X x (U x)) (U x)
  have hα : ContMDiff I 𝓘(Real, Real) ∞ α := tangentSectionAction_contMDiff X u.contMDiff
  have hS : ContMDiff I 𝓘(Real, Real) ∞ S := normGradSqFun_contMDiff g u.contMDiff
  have hpoint (x : M) :
      2 * tangentSectionAction U α x = 2 * A x + tangentSectionAction X S x := by
    have hmc : Geometry.Connection.IsMetricCompatible (LeviCivita g) g :=
      Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible g
    have h₁ := hmc.apply (x := x) X.mdifferentiableAt U.mdifferentiableAt (U x)
    have h₂ := hmc.apply (x := x) U.mdifferentiableAt U.mdifferentiableAt (X x)
    have heq : α = fun y => g.inner y (X y) (U y) :=
      funext fun y => tangentSectionAction_eq_inner_grad_g g u X y
    change tangentSectionAction U (fun y => g.inner y (X y) (U y)) x =
      A x + g.inner x (X x) ((LeviCivita g) U x (U x)) at h₁
    rw [← heq] at h₁
    change tangentSectionAction X S x =
      g.inner x ((LeviCivita g) U x (X x)) (U x) +
        g.inner x (U x) ((LeviCivita g) U x (X x)) at h₂
    have hh : g.inner x (X x) ((LeviCivita g) U x (U x)) =
        g.inner x ((LeviCivita g) U x (X x)) (U x) := by
      rw [g.symm]
      change g.inner x ((LeviCivita g) (fun y => gradFun g u y) x (U x)) (X x) =
        g.inner x ((LeviCivita g) (fun y => gradFun g u y) x (X x)) (U x)
      rw [← Geometry.Connection.hessFun_eq_cov_grad g u.contMDiff,
        ← Geometry.Connection.hessFun_eq_cov_grad g u.contMDiff]
      exact hessFun_symm_of_boundaryless g u.contMDiff x (U x) (X x)
    rw [hh] at h₁
    rw [g.symm x (U x)] at h₂
    linarith
  have hA : Continuous A := by
    have hAeq : A = fun x => tangentSectionAction U α x -
        (1 / 2 : Real) * tangentSectionAction X S x := by
      funext x
      linarith [hpoint x]
    rw [hAeq]
    exact (tangentSectionAction_contMDiff U hα).continuous.sub
      ((tangentSectionAction_contMDiff X hS).continuous.const_mul _)
  have hAint := Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g hA
    (HasCompactSupport.of_compactSpace A)
  have hXSint := Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g
    (tangentSectionAction_contMDiff X hS).continuous
    (HasCompactSupport.of_compactSpace (tangentSectionAction X S))
  have hi : 2 * (∫ x, tangentSectionAction U α x ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      2 * (∫ x, A x ∂riemannianVolumeMeasure (I := I) (M := M) g) +
        ∫ x, tangentSectionAction X S x ∂riemannianVolumeMeasure (I := I) (M := M) g := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hAint.const_mul 2) hXSint]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  rw [integral_tangentSectionAction_eq_neg_integral_smul_divergence g hα U
      (HasCompactSupport.of_compactSpace U),
    integral_tangentSectionAction_eq_neg_integral_smul_divergence g hS X
      (HasCompactSupport.of_compactSpace X)] at hi
  have hcomm : (∫ x, α x * divergenceG g U x ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, ΔG g u x * tangentSectionAction X u x ∂riemannianVolumeMeasure (I := I) (M := M) g := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => mul_comm _ _
  rw [hcomm] at hi
  change 2 * (∫ x, ΔG g u x * tangentSectionAction X u x ∂riemannianVolumeMeasure (I := I) (M := M) g) =
    (∫ x, S x * divergenceG g X x ∂riemannianVolumeMeasure (I := I) (M := M) g) -
      2 * (∫ x, A x ∂riemannianVolumeMeasure (I := I) (M := M) g)
  linarith

theorem rellich_identity_of_conformal (g : SmoothRiemannianMetric I M)
    (u : C^∞⟮I, M; Real⟯) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : Geometry.IsConformalVectorField g X) :
    2 * (∫ x, ΔG g u x * tangentSectionAction X u x
      ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      (1 - 2 / Module.finrank Real E) *
        ∫ x, normGradSqFun g u x * divergenceG g X x
          ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  have hpoint (x : M) :
      g.inner x ((LeviCivita g) X x (gradG g u x)) (gradG g u x) =
        (1 / Module.finrank Real E) * (normGradSqFun g u x * divergenceG g X x) := by
    have h := (Geometry.isConformalVectorField_iff_covariantDerivative_eq_divergence g X).mp
      hX x (gradG g u x) (gradG g u x)
    rw [g.symm x (gradG g u x)] at h
    change _ + _ = (2 / Module.finrank Real E) * divergenceG g X x * normGradSqFun g u x at h
    apply mul_left_cancel₀ (two_ne_zero : (2 : Real) ≠ 0)
    calc
      _ = _ := (two_mul _).trans h
      _ = _ := by ring
  rw [rellich_identity]
  simp_rw [hpoint]
  rw [integral_const_mul]
  ring

theorem integral_laplacian_mul_tangentSectionAction_eq_zero_of_conformal_of_finrank_eq_two
    (hn : Module.finrank Real E = 2) (g : SmoothRiemannianMetric I M)
    (u : C^∞⟮I, M; Real⟯) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : Geometry.IsConformalVectorField g X) :
    (∫ x, ΔG g u x * tangentSectionAction X u x
      ∂riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  have h := rellich_identity_of_conformal g u X hX
  rw [hn] at h
  norm_num at h
  exact h

theorem integral_divergence_mul_sq (g : SmoothRiemannianMetric I M)
    (u : C^∞⟮I, M; Real⟯) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (∫ x, divergenceG g X x * u x ^ 2
      ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      -2 * ∫ x, u x * tangentSectionAction X u x
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  have h := integral_tangentSectionAction_mul_add_eq_neg g u.contMDiff u.contMDiff X
    (HasCompactSupport.of_compactSpace X)
  have hleft : (∫ x, tangentSectionAction X u x * u x + u x * tangentSectionAction X u x
      ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      2 * ∫ x, u x * tangentSectionAction X u x
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  have hright : (∫ x, u x * u x * divergenceG g X x
      ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, divergenceG g X x * u x ^ 2
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  rw [hleft, hright] at h
  linarith

theorem integral_divergence_mul_sq_eq_zero_of_laplacian_eq_zero
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hu : ∀ x, ΔG g u x = 0) :
    (∫ x, divergenceG g X x * u x ^ 2
      ∂riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  have henergy : (∫ x, normGradSqFun g u x
      ∂riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
    have h := green_first_integral_inner_grad_eq_neg_integral_smul_laplacian g
      u.contMDiff u.contMDiff (HasCompactSupport.of_compactSpace (u : M → Real))
    change (∫ x, normGradSqFun g u x
      ∂riemannianVolumeMeasure (I := I) (M := M) g) =
        -∫ x, u x * ΔG g u x ∂riemannianVolumeMeasure (I := I) (M := M) g at h
    simpa only [hu, mul_zero, integral_zero, neg_zero] using h
  have hS := Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g
    (normGradSqFun_contMDiff g u.contMDiff).continuous
    (HasCompactSupport.of_compactSpace (normGradSqFun g u))
  have hz := (integral_eq_zero_iff_of_nonneg (normGradSqFun_nonneg g u) hS).mp henergy
  have ha : (∫ x, u x * tangentSectionAction X u x
      ∂riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hz] with x hx
    have hd := normGradSqFun_eq_zero_iff.mp hx
    have ha : tangentSectionAction X u x = 0 := by
      rw [tangentSectionAction_def, hd]
      rfl
    simp only [ha, mul_zero, Pi.zero_apply]
  rw [integral_divergence_mul_sq, ha, mul_zero]

theorem integral_divergence_mul_sq_eq_zero_of_conformal_of_eigenfunction
    (hn : Module.finrank Real E = 2) (g : SmoothRiemannianMetric I M)
    (u : C^∞⟮I, M; Real⟯) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : Geometry.IsConformalVectorField g X) {eigenvalue : Real}
    (hu : ∀ x, ΔG g u x = -eigenvalue * u x) :
    (∫ x, divergenceG g X x * u x ^ 2
      ∂riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  by_cases heigenvalue : eigenvalue = 0
  · apply integral_divergence_mul_sq_eq_zero_of_laplacian_eq_zero g u X
    simpa only [heigenvalue, neg_zero, zero_mul] using hu
  have h := integral_laplacian_mul_tangentSectionAction_eq_zero_of_conformal_of_finrank_eq_two
    hn g u X hX
  have heq : (∫ x, ΔG g u x * tangentSectionAction X u x
      ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      -eigenvalue * ∫ x, u x * tangentSectionAction X u x
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by dsimp only; rw [hu]; ring
  rw [heq] at h
  have ha := (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr heigenvalue)
  rw [integral_divergence_mul_sq, ha, mul_zero]

end DifferentialGeometry.Integral.DivergenceTheorem
