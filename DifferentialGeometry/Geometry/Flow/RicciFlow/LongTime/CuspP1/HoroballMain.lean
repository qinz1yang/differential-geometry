import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HoroballHadamard
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HoroballWarp
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HoroballFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HoroballCusp
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PeripheralCover

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic Set Function Bundle GC.Endpoint
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Hadamard for the finite-volume hyperbolic model (curvature `-1/4`): no null-homotopic
nonconstant geodesic loops. -/
theorem horo_hadamard_CPF3 (Hm : FiniteVolumeHyperbolicModel.{u}) {a : ℝ} (ha : 0 < a)
    {c : ℝ → Hm.Carrier}
    (hgeo : Riemannian.Geodesic.IsGeodesicOn (I := 𝓡 3) Hm.metric c (Ioo (-a) a))
    (hcont : ContinuousOn c (Icc (-a) a))
    (P : C(unitInterval, Hm.Carrier)) (hP : ∀ s : unitInterval, P s = c (-a + 2 * a * s))
    (hnull : P.HomotopicRel (ContinuousMap.const unitInterval (c (-a))) {0, 1}) :
    ∀ τ ∈ Icc (-a) a, c τ = c 0 := by
  let g := Hm.metric
  have hsec : GC.Geometry.HasConstantSectionalCurvature g (-(1 / 4 : ℝ)) := Hm.curvature
  have hR : ∀ (x : Hm.Carrier) (v Y : TangentSpace (𝓡 3) x),
      g.inner x (riemannOp (LeviCivita (I := 𝓡 3) g) x v Y Y) v ≤ 0 := by
    intro x v Y
    rw [GC.Geometry.riemannOp_eq_smul_of_hasConstantSectionalCurvature hsec x v Y Y]
    simp only [map_smul, map_sub, smul_apply, sub_apply, smul_eq_mul]
    have hcs := SmoothRiemannianMetric.metric_inner_cauchy_schwarz_sq g x v Y
    rw [g.symm x Y v]
    nlinarith
  let : IsManifold (𝓡 3) 1 Hm.Carrier :=
    IsManifold.of_le (I := 𝓡 3) (M := Hm.Carrier) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace Hm.Carrier := Manifold.metrizableSpace (𝓡 3) Hm.Carrier
  let : T3Space Hm.Carrier := inferInstance
  let : RiemannianBundle (fun x : Hm.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E3 (fun x : Hm.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace Hm.Carrier := EMetricSpace.ofRiemannianMetric (𝓡 3) Hm.Carrier
  let : CompleteSpace Hm.Carrier := Hm.complete.complete
  have hEg : IsMetricNorm (I := 𝓡 3) (M := Hm.Carrier) g := fun z v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := 𝓡 3) g z v
  exact geodesic_loop_const_of_nullhomotopic_CPF3 (I := 𝓡 3) g hEg hR ha hgeo hcont P hP hnull

end GC.LongTime.CuspP1
