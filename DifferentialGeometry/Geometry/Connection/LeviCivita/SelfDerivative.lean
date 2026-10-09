import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

open Connection Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The self covariant derivative vanishes wherever the original field vanishes. -/
theorem tsupport_leviCivita_self_subset
    (g : SmoothRiemannianMetric I M) (X : ∀ x : M, TangentSpace I x) :
    tsupport (fun x => (LeviCivita (I := I) g).toFun X x (X x)) ⊆ tsupport X := by
  apply closure_mono
  intro x hx hxX
  exact hx ((congrArg ((LeviCivita (I := I) g).toFun X x) hxX).trans (map_zero _))

theorem hasCompactSupport_leviCivita_self
    (g : SmoothRiemannianMetric I M) (X : ∀ x : M, TangentSpace I x)
    (hXc : HasCompactSupport X) :
    HasCompactSupport (fun x => (LeviCivita (I := I) g).toFun X x (X x)) :=
  hXc.of_isClosed_subset (isClosed_tsupport _) (tsupport_leviCivita_self_subset g X)

variable [I.Boundaryless] [T2Space M]

/-- Smoothness of the actual ambient acceleration field, from the existing smooth
Levi-Civita connection engine. -/
theorem contMDiff_leviCivita_self
    (g : SmoothRiemannianMetric I M) (X : ∀ x : M, TangentSpace I x)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, X x⟩ : TangentBundle I M))) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, (LeviCivita (I := I) g).toFun X x (X x)⟩ : TangentBundle I M)) := by
  have hX' : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (fun x => (⟨x, X x⟩ : TangentBundle I M)) := by
    rw [ENat.coe_top_add_one]
    exact hX
  exact contMDiffOn_univ.mp (covApply_contMDiffOn (cov := LeviCivita (I := I) g) hX hX')

end DifferentialGeometry.Geometry
