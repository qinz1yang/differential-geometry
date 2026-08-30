import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator Connection

set_option backward.isDefEq.respectTransparency false in
theorem roundThreeCylinderShrinkerPotential_hessian
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (u v : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
    hessFun (I := (𝓡 2).prod 𝓘(Real, Real)) roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential x u v =
      (1 / 2 : Real) * inner Real u.2 v.2 := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  have hprod := Operator.hessFun_prod
    (I := 𝓡 2) (J := 𝓘(Real, Real))
    roundTwoSphereShrinkerMetric (euclideanMetric (E := Real))
    roundTwoSphereShrinkerPotential (gaussianPotential (E := Real)) x u v
  have hsphere (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
      (a b : TangentSpace (𝓡 2) y) :
      hessFun (I := 𝓡 2) roundTwoSphereShrinkerMetric
        roundTwoSphereShrinkerPotential y a b = 0 := by
    let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) := ⟨by simp⟩
    simpa [roundTwoSphereShrinkerMetric, roundTwoSphereShrinkerPotential,
      roundSphereShrinkerPotential] using
      (roundSphereShrinkerPotential_hessian
        (A := EuclideanSpace Real (Fin 3)) (n := 2) (by decide) y a b)
  calc
    hessFun (I := (𝓡 2).prod 𝓘(Real, Real)) roundThreeCylinderShrinkerMetric
        roundThreeCylinderShrinkerPotential x u v =
      hessFun (I := (𝓡 2).prod 𝓘(Real, Real))
        (roundTwoSphereShrinkerMetric.prod (euclideanMetric (E := Real)))
        (fun q : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real =>
          roundTwoSphereShrinkerPotential q.1 + gaussianPotential q.2) x u v := by
            rfl
    _ = hessFun (I := 𝓡 2) roundTwoSphereShrinkerMetric
          roundTwoSphereShrinkerPotential x.1 u.1 v.1 +
        hessFun (I := 𝓘(Real, Real)) (euclideanMetric (E := Real))
          (gaussianPotential (E := Real)) x.2 u.2 v.2 := hprod
    _ = (1 / 2 : Real) * inner Real u.2 v.2 := by
      rw [hsphere, gaussianPotential_hessian]
      simp

set_option backward.isDefEq.respectTransparency false in
theorem roundThreeCylinderShrinkerPotential_tangential_hessian
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (u v : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x)
    (hu : u.2 = 0) (hv : v.2 = 0) :
    hessFun (I := (𝓡 2).prod 𝓘(Real, Real)) roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential x u v = 0 := by
  rw [roundThreeCylinderShrinkerPotential_hessian, hu, hv]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem roundThreeCylinderShrinkerPotential_mixed_hessian
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (u v : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x)
    (hu : u.2 = 0) :
    hessFun (I := (𝓡 2).prod 𝓘(Real, Real)) roundThreeCylinderShrinkerMetric
    roundThreeCylinderShrinkerPotential x u v = 0 := by
  simpa [hu] using
    (roundThreeCylinderShrinkerPotential_hessian x u v)

set_option backward.isDefEq.respectTransparency false in
theorem roundThreeCylinderShrinkerPotential_line_hessian
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (u v : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
    hessFun (I := (𝓡 2).prod 𝓘(Real, Real)) roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential x u v =
      (1 / 2 : Real) * inner Real u.2 v.2 :=
  roundThreeCylinderShrinkerPotential_hessian x u v

theorem roundThreeCylinderShrinkerPotential_line_restriction
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    (fun t : Real => roundThreeCylinderShrinkerPotential (y, t)) =
      (fun t : Real => 1 + t ^ 2 / 4) := by
  funext t
  exact roundThreeCylinderShrinkerPotential_apply (y, t)

end DifferentialGeometry.Geometry
