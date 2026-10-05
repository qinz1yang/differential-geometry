import DifferentialGeometry.Geometry.Thurston.FlatPrime
import DifferentialGeometry.Geometry.Exponential.Flat.FlatMetricCover

/-!
# Isometric covering coordinates of the original Euclidean geometric structure

The original geometric structure supplies its curvature and complete metric. Normalizing the
actual exponential covering gives Euclidean source coordinates with isometric deck maps while
retaining the same closed target manifold.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Bundle Manifold GC GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.FlatSurface

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem exists_isometricCover_of_euclidean (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .euclidean) :
    ∃ p : E3 → P.Carrier, IsCoveringMap p ∧ Function.Surjective p ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p ∧
      ∀ γ : coveringDeckGroup p, Isometry (γ.1 : E3 → E3) := by
  have hsec := GC.Geometry.hasConstantSectionalCurvature_of_hasThurstonAtlas_euclidean
    (hg ▸ g.atlas)
  have hR : ∀ x (X Y Z : TangentSpace (𝓡 3) x),
      riemannOp (LeviCivita g.metric) x X Y Z = 0 := by
    intro x X Y Z
    exact (GC.Geometry.riemannOp_eq_smul_of_hasConstantSectionalCurvature hsec x X Y Z).trans
      (zero_smul ℝ _)
  let instManifoldOne : IsManifold (𝓡 3) 1 P.Carrier := IsManifold.of_le
    (I := 𝓡 3) (M := P.Carrier) (n := (∞ : WithTop ℕ∞)) (by decide)
  let instMetrizable : TopologicalSpace.MetrizableSpace P.Carrier :=
    Manifold.metrizableSpace (𝓡 3) P.Carrier
  let instRegular : T3Space P.Carrier := inferInstance
  let instBundle : RiemannianBundle (fun x : P.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨g.metric.toRiemannianMetric⟩
  let instContinuous : IsContinuousRiemannianBundle E3
      (fun x : P.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨⟨g.metric.inner, g.metric.contMDiff.continuous, fun x v w => rfl⟩⟩
  let instMetric : EMetricSpace P.Carrier := EMetricSpace.ofRiemannianMetric (𝓡 3) P.Carrier
  let instComplete : CompleteSpace P.Carrier := g.complete.complete
  have hEnorm : IsMetricNorm (I := 𝓡 3) (M := P.Carrier) g.metric :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := 𝓡 3) g.metric x v
  obtain ⟨p, hl, hp, hs, hi⟩ := exists_isometric_flat_cover
    (E := E3) (I := 𝓡 3) (M := P.Carrier) g.metric hEnorm hR
  have hAll : IsCoveringMap p ∧ Function.Surjective p ∧
      IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E3))) (𝓡 3) ∞ p ∧
      ∀ γ : coveringDeckGroup p,
        Isometry (γ.1 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E3)) →
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E3))) := ⟨hp, hs, hl, hi⟩
  have hex : ∃ q : EuclideanSpace ℝ (Fin (Module.finrank ℝ E3)) → P.Carrier,
      IsCoveringMap q ∧ Function.Surjective q ∧
      IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E3))) (𝓡 3) ∞ q ∧
      ∀ γ : coveringDeckGroup q,
        Isometry (γ.1 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E3)) →
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E3))) := ⟨p, hAll⟩
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  rw [hdim] at hex
  exact hex

end DifferentialGeometry.Geometry.FlatSurface
