import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.ConstantPotential
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Soliton

open DifferentialGeometry.Geometry

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace Real A]
  [FiniteDimensional Real A] {n : Nat} [Fact (Module.finrank Real A = n + 1)]

theorem canonicalFlowMap_roundSphere
    (hn : 2 ≤ n) (s : Real) (x : Metric.sphere (0 : A) 1) :
    let _ : ConnectedSpace (Metric.sphere (0 : A) 1) := Subtype.connectedSpace
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank
        (by rw [show Module.finrank Real A = n + 1 from Fact.out]; omega)) 0 zero_le_one)
    canonicalFlowMap (roundSphereShrinkerMetric (A := A) hn)
      roundSphereShrinkerPotential 1 (roundSphereShrinkerMetric_complete hn)
      (gradientRicciSoliton_roundSphere hn) s x = x := by
  let _ : ConnectedSpace (Metric.sphere (0 : A) 1) := Subtype.connectedSpace
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank
      (by rw [show Module.finrank Real A = n + 1 from Fact.out]; omega)) 0 zero_le_one)
  exact canonicalFlowMap_const (roundSphereShrinkerMetric hn) _ _
    (roundSphereShrinkerMetric_complete hn) (gradientRicciSoliton_roundSphere hn) s x

theorem canonicalMetric_roundSphere
    (hn : 2 ≤ n) {t : Real} (ht : t ∈ canonicalTimeDomain 1) :
    let _ : ConnectedSpace (Metric.sphere (0 : A) 1) := Subtype.connectedSpace
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank
        (by rw [show Module.finrank Real A = n + 1 from Fact.out]; omega)) 0 zero_le_one)
    canonicalMetric (roundSphereShrinkerMetric (A := A) hn)
      roundSphereShrinkerPotential 1 (roundSphereShrinkerMetric_complete hn)
      (gradientRicciSoliton_roundSphere hn) ht =
        scaleMetric (1 - t) (by simpa using mem_canonicalTimeDomain_iff.mp ht)
          (roundSphereShrinkerMetric (A := A) hn) := by
  let _ : ConnectedSpace (Metric.sphere (0 : A) 1) := Subtype.connectedSpace
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank
      (by rw [show Module.finrank Real A = n + 1 from Fact.out]; omega)) 0 zero_le_one)
  simpa only [roundSphereShrinkerPotential, one_mul] using canonicalMetric_const (roundSphereShrinkerMetric (A := A) hn)
    ((n : Real) / 2) 1 (roundSphereShrinkerMetric_complete hn)
    (gradientRicciSoliton_roundSphere hn) ht

end DifferentialGeometry.PDE.RicciFlow.Soliton
