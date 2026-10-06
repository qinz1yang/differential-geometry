import DifferentialGeometry.Geometry.Thurston.SphericalStructureStandard
import DifferentialGeometry.Geometry.Thurston.CyclicSphericalRecognition
import DifferentialGeometry.Geometry.Thurston.QuaternionPrismConjugateRaw_X127_R2b
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyClosedModel
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierDiffeomorphTransport

/-!
# X127-S: reduction of the admitted spherical recognition to the standard space forms

The admitted statement `rawGraphPresentation_of_sphericalSpaceForm` asks for a raw graph
presentation of every closed connected carrier `W` with a spherical Thurston structure.
`exists_sphericalSpaceForm_diffeomorph_of_sphericalStructure_X127S` is the first half of its proof:
`W` is diffeomorphic to the standard space form `S³/Γ` of a finite free orientation preserving
group `Γ ⊂ O(4)` (`SphericalSpaceFormGroup`). The second half is a raw presentation of every
`S³/Γ`; the families done so far are the cyclic groups (X117) and the generalized quaternion
(prism) groups with all their `O(4)`-conjugates (X127 G1), recorded by
`nonempty_rawGraphPresentation_spaceForm_known_X127S` and transported to `W` by
`nonempty_rawGraphPresentation_of_diffeomorph_spaceForm_known_X127S`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Geometry
open DifferentialGeometry.Geometry
  (exists_orientedDiffeomorph_sphericalSpaceForm_of_constantPositiveSectionalCurvature)
open scoped Manifold ContDiff

attribute [local instance] uliftChartedSpace isManifold_ulift

universe u

namespace GC.Geometry.SphericalSpaceFormReductionX127S

theorem exists_sphericalSpaceForm_diffeomorph_of_sphericalStructure_X127S
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (hboundary : W.model.boundary W.Carrier = ∅)
    (G : GeometricStructure W.model W.Carrier) (hG : G.model = .spherical) :
    ∃ H : SphericalSpaceFormGroup,
      Nonempty (W.Carrier ≃ₘ⟮W.model, 𝓡 3⟯ H.manifold.Carrier) := by
  obtain ⟨Q, e, -⟩ := Assembly.exists_closedModel_of_boundary_eq_empty W hboundary
  let S := G.pullback e.symm
  have hA : HasThurstonAtlas S.metric .spherical := (show S.model = .spherical from hG) ▸ S.atlas
  obtain ⟨H, ⟨f⟩⟩ :=
    exists_orientedDiffeomorph_sphericalSpaceForm_of_constantPositiveSectionalCurvature
      Q S.metric (constantPositiveSectionalCurvatureMetric_of_hasThurstonAtlas_spherical hA)
  exact ⟨H, ⟨e.trans f.1⟩⟩

theorem nonempty_rawGraphPresentation_spaceForm_known_X127S (H : SphericalSpaceFormGroup)
    (hH : IsCyclic H.group ∨ ∃ (n : ℕ) (_ : NeZero n)
      (φ : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)),
      H = conjSphericalSpaceFormGroup (QuaternionPrismX127R3.spaceForm_X127 n) φ) :
    Nonempty (RawGraphPresentation (NoCuts.carrier H.manifold.ulift.{0, u})) := by
  rcases hH with hcyc | ⟨n, hn, φ, rfl⟩
  · exact rawGraphPresentation_of_sphericalSpaceForm_cyclic H
  · exact QuaternionPrismConjugateRawX127.nonempty_rawGraphPresentation_conjugatePrism_X127 n φ

theorem nonempty_rawGraphPresentation_of_diffeomorph_spaceForm_known_X127S
    (W : CompactCarrier.{u}) (H : SphericalSpaceFormGroup)
    (hH : IsCyclic H.group ∨ ∃ (n : ℕ) (_ : NeZero n)
      (φ : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)),
      H = conjSphericalSpaceFormGroup (QuaternionPrismX127R3.spaceForm_X127 n) φ)
    (e : W.Carrier ≃ₘ⟮W.model, 𝓡 3⟯ H.manifold.Carrier) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨R⟩ := nonempty_rawGraphPresentation_spaceForm_known_X127S.{u} H hH
  have : PreconnectedSpace (NoCuts.carrier H.manifold.ulift.{0, u}).Carrier :=
    inferInstanceAs (PreconnectedSpace H.manifold.ulift.{0, u}.Carrier)
  exact nonempty_rawGraphPresentation_of_carrierDiffeomorph R
    ((uliftDiffeomorph.{0, u} (𝓡 3) H.manifold.Carrier).symm.trans e.symm)

end GC.Geometry.SphericalSpaceFormReductionX127S
