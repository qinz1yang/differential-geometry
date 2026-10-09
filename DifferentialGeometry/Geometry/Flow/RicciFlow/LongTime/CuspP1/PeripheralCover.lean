import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PeripheralReduction
import DifferentialGeometry.Geometry.Thurston.HyperbolicPieceCover
import DifferentialGeometry.Geometry.Thurston.ConstantCurvatureAtlas

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic Set Function Bundle
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

-- Cartan–Hadamard for the finite-volume hyperbolic model (curvature `-1/4`, complete):
-- `ℝ³ → H` is a surjective covering and a local diffeomorphism.
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_isCoveringMap_finiteVolumeModel_CPF (H : FiniteVolumeHyperbolicModel.{u}) :
    ∃ p : E3 → H.Carrier, IsCoveringMap p ∧ Function.Surjective p ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p := by
  let g := H.metric
  have hsec : GC.Geometry.HasConstantSectionalCurvature g (-(1 / 4 : ℝ)) := H.curvature
  have hR : ∀ (x : H.Carrier) (v Y : TangentSpace (𝓡 3) x),
      g.inner x (riemannOp (LeviCivita (I := 𝓡 3) g) x v Y Y) v ≤ 0 := by
    intro x v Y
    rw [GC.Geometry.riemannOp_eq_smul_of_hasConstantSectionalCurvature hsec x v Y Y]
    simp only [map_smul, map_sub, smul_apply, sub_apply, smul_eq_mul]
    have hcs := SmoothRiemannianMetric.metric_inner_cauchy_schwarz_sq g x v Y
    rw [g.symm x Y v]
    nlinarith
  let : IsManifold (𝓡 3) 1 H.Carrier :=
    IsManifold.of_le (I := 𝓡 3) (M := H.Carrier) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace H.Carrier := Manifold.metrizableSpace (𝓡 3) H.Carrier
  let : T3Space H.Carrier := inferInstance
  let : RiemannianBundle (fun x : H.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E3 (fun x : H.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace H.Carrier := EMetricSpace.ofRiemannianMetric (𝓡 3) H.Carrier
  let : CompleteSpace H.Carrier := H.complete.complete
  have hEg : IsMetricNorm (I := 𝓡 3) (M := H.Carrier) g := fun z v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := 𝓡 3) g z v
  exact ⟨_, GC.Geometry.framedExpMap_isCoveringMap_of_nonpos g hEg H.basepoint hR,
    GC.Geometry.framedExpMap_surjective g hEg H.basepoint,
    GC.Geometry.framedExpMap_isLocalDiffeomorph_of_nonpos g hEg H.basepoint hR⟩

end GC.LongTime.CuspP1
