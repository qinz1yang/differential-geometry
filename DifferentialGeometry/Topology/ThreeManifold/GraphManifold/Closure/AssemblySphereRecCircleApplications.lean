import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCircle

/-!
# Consumers of packet S2, circle region (lane ASM-SPH)

* `CircleRegion.exists_restrictBase`: a circle region restricted to an open base set containing the
  cornered base, the rounded base and the corner-chart targets keeps its region and rounded region,
  with the saturated domain `proj⁻¹ O`.
* `DecompositionCertificate.exists_liftedCircleRegion`: for a sphere seam `c` and its
  cut-and-capped data `X`, the retained circle region of the certificate becomes a circle region of
  the capped carrier whose cornered and rounded regions are the transports of the old ones.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **Restriction of a circle region to an open base set.** -/
theorem CircleRegion.exists_restrictBase {W : CompactCarrier.{u}} (R : CircleRegion W)
    (O : TopologicalSpace.Opens R.Base) (hcorner : R.cornerBase ⊆ O)
    (hround : {b | R.rounding b ≤ 0} ⊆ O) (hchart : ∀ k, (R.cornerChart k).target ⊆ O) :
    ∃ R' : CircleRegion W, R'.region = R.region ∧ R'.rounded = R.rounded ∧
      (R'.domain : Set W.Carrier) = Subtype.val '' (R.proj ⁻¹' (O : Set R.Base)) :=
  ⟨R.restrictBase O hcorner hround hchart, R.region_restrictBase hcorner hround hchart,
    R.rounded_restrictBase hcorner hround hchart, R.restrictBase_domain hcorner hround hchart⟩

/-- **The retained circle region lifts into the capped carrier.** -/
theorem DecompositionCertificate.exists_liftedCircleRegion {W : CompactCarrier.{u}} {n : ℕ}
    {E : BoundaryTori W n} (D : DecompositionCertificate W E) (c : Fin D.sphereSeamCount)
    (X : SphereCutCapped W (D.sphereSeam c) E) :
    ∃ R' : CircleRegion X.Q, R'.region = X.transport '' D.circ.region ∧
      R'.rounded = X.transport '' D.circ.rounded :=
  ⟨D.liftCircleRegion c X, D.region_liftCircleRegion c X, D.rounded_liftCircleRegion c X⟩

end GC.GraphManifold.Assembly
