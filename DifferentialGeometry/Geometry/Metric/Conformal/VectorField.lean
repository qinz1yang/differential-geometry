import DifferentialGeometry.Geometry.Metric.LieDerivative.Cartan
import DifferentialGeometry.Geometry.Connection.LeviCivita.Divergence.FrameInvariance

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry

open Bundle
open Connection (LeviCivita)
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def IsConformalVectorField (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : Prop :=
  ∃ φ : M → Real, ∀ (x : M) (v w : TangentSpace I x),
    g.inner x ((LeviCivita g) X x v) w + g.inner x v ((LeviCivita g) X x w) =
      φ x * g.inner x v w

theorem isConformalVectorField_iff_lieDerivMetric [T2Space M] [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    IsConformalVectorField g X ↔
      ∃ φ : M → Real, ∀ (x : M) (v w : TangentSpace I x),
        PDE.DeTurck.lieDerivMetric g X x v w = φ x * g.inner x v w := by
  simp only [IsConformalVectorField, PDE.RicciFlow.Pullback.cartan_formula_for_lie_deriv_metric]

theorem isConformalVectorField_of_finrank_eq_zero
    (hn : Module.finrank Real E = 0) (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    IsConformalVectorField g X := by
  have : Subsingleton E := Module.finrank_zero_iff.mp hn
  refine ⟨0, fun x v w => ?_⟩
  have hv : v = 0 := Subsingleton.elim (α := E) _ _
  simp only [hv, map_zero, zero_apply, add_zero, mul_zero]


open DifferentialGeometry.Integral.DivergenceTheorem (divergenceG)

variable [I.Boundaryless] [T2Space M]

theorem conformal_factor_mul_finrank_eq_two_mul_divergence
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {φ : M → Real}
    (hX : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x ((LeviCivita g) X x v) w + g.inner x v ((LeviCivita g) X x w) =
        φ x * g.inner x v w) (x : M) :
    φ x * Module.finrank Real E = 2 * divergenceG g X x := by
  classical
  let b : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x) :=
    Module.finBasis Real E
  let q := Tensor0SBundle.basisInvMetric (I := I) g x b
  have hq := Tensor0SBundle.basisInvMetric_isInverse (I := I) g x b
  have hqs := Tensor0SBundle.basisInvMetric_symm (I := I) g x b
  have hd : divergenceG g X x = ∑ i, ∑ j,
      q i j * g.inner x ((LeviCivita g) X x (b i)) (b j) := by
    rw [← Connection.metricTracePair0SAt_nablaCov_eq_divergence,
      Operator.metricTracePair0SAt_eq_sum_basis g b q hq]
    simp only [Connection.nablaCovTensor_apply, Curvature.vec2]
    rfl
  have ht : (∑ i, ∑ j, q i j * g.inner x (b i) ((LeviCivita g) X x (b j))) =
      ∑ i, ∑ j, q i j * g.inner x ((LeviCivita g) X x (b i)) (b j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show q j i = q i j from hqs j i, g.symm]
  have hg : (∑ i, ∑ j, q i j * g.inner x (b i) (b j)) =
      (Module.finrank Real E : Real) := by
    calc
      (∑ i, ∑ j, q i j * g.inner x (b i) (b j)) = ∑ i, (1 : Real) := by
        apply Finset.sum_congr rfl
        intro i _
        simpa [q, g.symm x (b i)] using (hq i i).1
      _ = _ := by simp
  calc
    φ x * Module.finrank Real E = ∑ i, ∑ j, q i j * (φ x * g.inner x (b i) (b j)) := by
      rw [← hg, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i, ∑ j, q i j * g.inner x ((LeviCivita g) X x (b i)) (b j)) +
        ∑ i, ∑ j, q i j * g.inner x (b i) ((LeviCivita g) X x (b j)) := by
      simp only [← hX x, mul_add, Finset.sum_add_distrib]
    _ = 2 * divergenceG g X x := by rw [ht, ← hd]; ring

theorem conformal_factor_eq_two_div_finrank_mul_divergence
    (hn : Module.finrank Real E ≠ 0) (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {φ : M → Real}
    (hX : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x ((LeviCivita g) X x v) w + g.inner x v ((LeviCivita g) X x w) =
        φ x * g.inner x v w) (x : M) :
    φ x = (2 / Module.finrank Real E) * divergenceG g X x := by
  have hn' : (Module.finrank Real E : Real) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h := conformal_factor_mul_finrank_eq_two_mul_divergence g X hX x
  apply (mul_right_cancel₀ hn')
  rw [h]
  field_simp

theorem isConformalVectorField_iff_covariantDerivative_eq_divergence
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    IsConformalVectorField g X ↔
      ∀ (x : M) (v w : TangentSpace I x),
        g.inner x ((LeviCivita g) X x v) w + g.inner x v ((LeviCivita g) X x w) =
          (2 / Module.finrank Real E) * divergenceG g X x * g.inner x v w := by
  constructor
  · rintro ⟨φ, hφ⟩ x v w
    by_cases hn : Module.finrank Real E = 0
    · have : Subsingleton E := Module.finrank_zero_iff.mp hn
      have hv : v = 0 := Subsingleton.elim (α := E) _ _
      simp only [hv, map_zero, zero_apply, add_zero, mul_zero]
    · rw [hφ, conformal_factor_eq_two_div_finrank_mul_divergence hn g X hφ x]
  · exact fun h => ⟨fun x => (2 / Module.finrank Real E) * divergenceG g X x, h⟩

end DifferentialGeometry.Geometry
