import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Product
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Sphere
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Gaussian

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Soliton
open DifferentialGeometry.Geometry

variable {k d : Nat}
private instance sphereFinrankFact :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin (k + 1))) = k + 1) := ⟨by simp⟩

theorem canonicalMetric_roundCylinder (hk : 2 ≤ k)
    (x : Real) (hx : x < 1) :
    let _ : ConnectedSpace (Metric.sphere (0 : EuclideanSpace Real (Fin (k + 1))) 1) :=
      Subtype.connectedSpace (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank
        (by simp; omega)) 0 zero_le_one)
    let g := roundSphereShrinkerMetric (A := EuclideanSpace Real (Fin (k + 1))) hk
    let h := euclideanMetric (E := EuclideanSpace Real (Fin d))
    let f := roundSphereShrinkerPotential (A := EuclideanSpace Real (Fin (k + 1))) (n := k)
    let u := f.comp ContMDiffMap.fst + (gaussianPotential (E := EuclideanSpace Real (Fin d))).comp ContMDiffMap.snd
    canonicalMetric (g.prod h) u 1
      (RiemannianMetricComplete.prod (roundSphereShrinkerMetric_complete hk) euclideanMetric_complete)
      (gradientRicciSoliton_prod (gradientRicciSoliton_roundSphere hk) gradientRicciSoliton_gaussian)
      (by change 0 < 1 - 1 * x; simpa only [one_mul] using sub_pos.mpr hx) =
      (scaleMetric (1 - x) (sub_pos.mpr hx) g).prod h := by
  let _ : ConnectedSpace (Metric.sphere (0 : EuclideanSpace Real (Fin (k + 1))) 1) :=
    Subtype.connectedSpace (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank
      (by simp; omega)) 0 zero_le_one)
  dsimp only
  rw [canonicalMetric_prod _ _ _ _ 1
    (roundSphereShrinkerMetric_complete hk) euclideanMetric_complete
    (gradientRicciSoliton_roundSphere hk) gradientRicciSoliton_gaussian]
  rw [canonicalMetric_gaussian]
  have hs := canonicalMetric_const
    (roundSphereShrinkerMetric (A := EuclideanSpace Real (Fin (k + 1))) hk)
    ((k : Real) / 2) 1 (roundSphereShrinkerMetric_complete hk)
    (gradientRicciSoliton_roundSphere hk)
    (by change 0 < 1 - 1 * x; simpa only [one_mul] using sub_pos.mpr hx)
  simp only [one_mul] at hs
  exact congrArg (fun q => q.prod (euclideanMetric (E := EuclideanSpace Real (Fin d)))) hs

end DifferentialGeometry.PDE.RicciFlow.Soliton
