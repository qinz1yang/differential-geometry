import DifferentialGeometry.Geometry.Thurston.Atlas
import DifferentialGeometry.Geometry.Thurston.ElementaryModels
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.PartialDiffeomorph
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormCovering
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.StandardCertificates
import DifferentialGeometry.Compat.Ch567.Topology.ThreeManifold.PoincareStandard

/-!
# Closed spherical structures are standard factors

Chapter 7, survey packet P5. A closed oriented `3`-manifold carrying a complete Thurston
structure modeled on the round `S³` is a standard factor
(`isStandardFactor_of_sphericalStructure`), hence geometrizes
(`geometrizes_of_sphericalStructure`). The spherical atlas gives sectional
curvature `1` (the converse direction of packet P4, re-derived here because
`ConstantCurvatureAtlas` cannot be imported next to `SphericalProductPiece`: both declare the
same auto-named `Fact` instance), and the space-form covering theorem
`exists_orientedDiffeomorph_sphericalSpaceForm_of_constantPositiveSectionalCurvature` produces an
oriented diffeomorphism onto `S³/Γ` for a `SphericalSpaceFormGroup` `Γ`.

A closed oriented `S² × ℝ` manifold is `S² × S¹` or `RP³ # RP³`, a standard connected sum but in
general not a standard factor; that classification is the named input
`SphericalProductStandardConnectedSum`, from which `geometrizes_of_sphericalProductStructure`
follows by `geometrizes_of_isPoincareStandard`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace GC.Geometry

universe u

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]

theorem constantPositiveSectionalCurvatureMetric_of_hasThurstonAtlas_spherical
    {g : SmoothRiemannianMetric (𝓡 3) M} (hA : HasThurstonAtlas g .spherical) :
    constantPositiveSectionalCurvatureMetric g := by
  refine ⟨1, one_pos, fun x X Y => ?_⟩
  obtain ⟨e, hx, he⟩ := hA x
  obtain ⟨y, hy, rfl⟩ : ∃ y ∈ e.source, e y = x :=
    ⟨e.symm x, e.map_target hx, e.right_inv hx⟩
  let L := (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ e hy
    ).mfderivToContinuousLinearEquiv (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  obtain ⟨a, rfl⟩ : ∃ a : TangentSpace (𝓡 3) y, mfderiv (𝓡 3) (𝓡 3) e y a = X :=
    ⟨L.symm X, L.apply_symm_apply X⟩
  obtain ⟨b, rfl⟩ : ∃ b : TangentSpace (𝓡 3) y, mfderiv (𝓡 3) (𝓡 3) e y b = Y :=
    ⟨L.symm Y, L.apply_symm_apply Y⟩
  let U : TopologicalSpace.Opens RoundThree := ⟨e.source, e.open_source⟩
  have hmet : ∀ z : U, ∀ v w : TangentSpace (𝓡 3) z,
      sphericalModelMetric.inner z.val v w = g.inner (e z.val)
        (mfderiv (𝓡 3) (𝓡 3) e z.val v) (mfderiv (𝓡 3) (𝓡 3) e z.val w) :=
    fun z v w => (he z.val z.property v w).symm
  rw [← metricRm04StandardAt_eq_of_partialDiffeomorph_restriction e U subset_rfl
      sphericalModelMetric g hmet ⟨y, hy⟩ a b b a, he y hy a a, he y hy b b,
    he y hy a b, one_mul]
  exact roundMetric_sec_value y a b

theorem isStandardFactor_of_sphericalStructure (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .spherical) :
    isStandardFactor P := by
  have hA : HasThurstonAtlas g.metric .spherical := hg ▸ g.atlas
  exact Or.inl
    (exists_orientedDiffeomorph_sphericalSpaceForm_of_constantPositiveSectionalCurvature P g.metric
      (constantPositiveSectionalCurvatureMetric_of_hasThurstonAtlas_spherical hA))

end GC.Geometry

namespace GC.Endpoint

universe u

theorem geometrizes_of_sphericalStructure (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .spherical) :
    Geometrizes P :=
  geometrizes_of_isStandardFactor P (GC.Geometry.isStandardFactor_of_sphericalStructure P g hg)

def SphericalProductStandardConnectedSum : Prop :=
  ∀ (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier),
    g.model = .sphericalProduct → isStandardConnectedSum P.Carrier

theorem geometrizes_of_sphericalProductStructure
    (hS : SphericalProductStandardConnectedSum.{u})
    (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .sphericalProduct) :
    Geometrizes P :=
  geometrizes_of_isPoincareStandard P (hS P g hg)

end GC.Endpoint
