import DifferentialGeometry.Geometry.Metric.Conformal.Basic
import DifferentialGeometry.Geometry.Metric.Conformal.VectorField
import DifferentialGeometry.Geometry.Operator.NormGradSq

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry

open Bundle
open Connection (LeviCivita)
open DifferentialGeometry.Integral.DivergenceTheorem (tangentSectionAction)
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [BoundarylessManifold I M]

private theorem lieDerivMetric_apply_sections
    (g : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    PDE.DeTurck.lieDerivMetric g X x (Y x) (Z x) =
      tangentSectionAction X (fun y => g.inner y (Y y) (Z y)) x -
        g.inner x (VectorField.mlieBracket I X Y x) (Z x) -
        g.inner x (Y x) (VectorField.mlieBracket I X Z x) := by
  have hm := (Connection.LeviCivita_isMetricCompatible g).apply
    (x := x) Y.mdifferentiableAt Z.mdifferentiableAt (X x)
  have hY := (CovariantDerivative.torsion_eq_zero_iff (LeviCivita g)).mp
    (Connection.LeviCivita_torsion_eq_zero g)
    (x := x) X.mdifferentiableAt Y.mdifferentiableAt
  have hZ := (CovariantDerivative.torsion_eq_zero_iff (LeviCivita g)).mp
    (Connection.LeviCivita_torsion_eq_zero g)
    (x := x) X.mdifferentiableAt Z.mdifferentiableAt
  rw [PDE.RicciFlow.Pullback.cartan_formula_for_lie_deriv_metric]
  change tangentSectionAction X (fun y => g.inner y (Y y) (Z y)) x = _ at hm
  rw [hm, ← hY, ← hZ]
  simp only [map_sub, sub_apply]
  ring

omit [FiniteDimensional Real E] [T2Space M] [BoundarylessManifold I M] in
private theorem tangentSectionAction_exp_two_mul
    (u : C^∞⟮I, M; Real⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    tangentSectionAction X (fun y => Real.exp (2 * u y)) x =
      2 * Real.exp (2 * u x) * tangentSectionAction X u x := by
  have hu := (u.contMDiff.mdifferentiableAt (by simp) :
    MDifferentiableAt I 𝓘(Real) (u : M → Real) x).hasMFDerivAt
  have htwo : HasMFDerivAt I 𝓘(Real) (fun y : M => 2 * u y) x
      ((2 : Real) • mfderiv I 𝓘(Real) u x) := hu.const_smul 2
  have hx := ((Real.hasDerivAt_exp (2 * u x)).hasFDerivAt.hasMFDerivAt.comp x htwo).mfderiv
  have happly := congrArg (fun F : TangentSpace I x →L[Real] Real => F (X x)) hx
  change tangentSectionAction X (fun y => Real.exp (2 * u y)) x =
    (2 * tangentSectionAction X u x) * Real.exp (2 * u x) at happly
  rw [happly]
  ring

theorem lieDerivMetric_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (v w : TangentSpace I x) :
    PDE.DeTurck.lieDerivMetric (conformalMetric g u) X x v w =
      Real.exp (2 * u x) * PDE.DeTurck.lieDerivMetric g X x v w +
        2 * tangentSectionAction X u x * (conformalMetric g u).inner x v w := by
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := E) (V := TangentSpace I) x v
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := E) (V := TangentSpace I) x w
  rw [← hY, ← hZ, lieDerivMetric_apply_sections, lieDerivMetric_apply_sections]
  simp_rw [conformalMetric_inner]
  have hcoeff : ContMDiff I 𝓘(Real) ∞ (fun y : M => Real.exp (2 * u y)) :=
    Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul u.contMDiff)
  have hpair := Operator.contMDiff_g_inner_of_smooth_sections g Y Z
  rw [Integral.DivergenceTheorem.tangent_mul X
    (hcoeff.mdifferentiableAt (by simp)) (hpair.mdifferentiableAt (by simp)),
    tangentSectionAction_exp_two_mul]
  ring

theorem isConformalVectorField_conformalMetric_iff
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    IsConformalVectorField (conformalMetric g u) X ↔ IsConformalVectorField g X := by
  rw [isConformalVectorField_iff_lieDerivMetric,
    isConformalVectorField_iff_lieDerivMetric]
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨fun x => φ x - 2 * tangentSectionAction X u x, fun x v w => ?_⟩
    have h := hφ x v w
    rw [lieDerivMetric_conformalMetric, conformalMetric_inner] at h
    apply mul_left_cancel₀ (Real.exp_ne_zero (2 * u x))
    nlinarith [h]
  · rintro ⟨φ, hφ⟩
    refine ⟨fun x => φ x + 2 * tangentSectionAction X u x, fun x v w => ?_⟩
    rw [lieDerivMetric_conformalMetric, hφ, conformalMetric_inner]
    ring

end DifferentialGeometry.Geometry
