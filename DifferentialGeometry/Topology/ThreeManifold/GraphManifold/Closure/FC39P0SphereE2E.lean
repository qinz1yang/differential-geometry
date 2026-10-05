import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointCertificate
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Sphere
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Refinement

/-!
# FC39 gate 1, end-to-end check: FC42 run on the real S³ strong certificate

The accepted FC42 final theorem (form (b),
`exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct`) and the strong-certificate
consumer `StrongCertificate.raw_or_aux_nonneg` are applied to the NON-VACUOUS strong certificate
`sphereStrongCertificate` of the one S³ configuration (two zero balls, one slim `S² × I`, two actual
handles, one sphere seam), every hypothesis discharged by real S³ data:

* `[ConnectedSpace sphereW.Carrier]` — the `connected` field of `standardThreeSphereLift` (an
  instance already, `ConnectedClosedOrientedManifold.connected`); named
  `connectedSpace_sphereW_E2E`;
* `hprod` — `sphereJointCertificate_rimProduct` (four rim-product clauses at two actual handles).

Results: `sphere_fc42_E2E` (FC42 on the certificate), `sphereStrongCertificate_raw_or_aux_nonneg_E2E`
(the strong consumer). The branch: the certificate has no closed zero vertex
(`sphereStrongCertificate_vertex_ne_closedZero_E2E`), so FC42's proof yields the RAW disjunct through
the μ-recursion (`sphereStrongCertificate_raw_E2E`, the same production packets); at the top level
there is no slim vertex over the circle (`sphereStrongCertificate_not_slimOverCircle_E2E`) and
`μ > 0` (`sphereStrongCertificate_sphereMeasure_pos_E2E`), so the first step is the sphere step at
the one sphere seam, not the torus assembly (L1). Consumers downstream: the chapter-14 interface
disjunction (`sphere_raw_or_closedGeometric_E2E`) and `Geometrizes standardThreeSphereLift`
(`sphere_geometrizes_E2E`). Finding recorded by `sphere_raw_clifford_E2E`: the raw disjunct is
already known for S³ without any certificate (the Clifford presentation), so this run tests the
satisfiability of the hypotheses, not the informativeness of the conclusion.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-! ## The connectedness hypothesis -/

/-- **(a)** The S³ carrier is connected (found by instance search through the `connected` field of
`standardThreeSphereLift`; named for citation). -/
theorem connectedSpace_sphereW_E2E : ConnectedSpace sphereW.Carrier :=
  inferInstance

/-! ## FC42 and the strong consumer on the real certificate -/

/-- **(b) FC42, form (b), on the real S³ certificate**: every hypothesis is S³ data. -/
theorem sphere_fc42_E2E :
    Nonempty (RawGraphPresentation sphereW) ∨
      (sphereW.model.boundary sphereW.Carrier = ∅ ∧
        ∃ g' : SmoothRiemannianMetric sphereW.model sphereW.Carrier,
          DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0) :=
  exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct sphereW
    sphereJointCertificate sphereJointCertificate_rimProduct

/-- **(b) The strong-certificate consumer on the real S³ strong certificate.** -/
theorem sphereStrongCertificate_raw_or_aux_nonneg_E2E :
    Nonempty (RawGraphPresentation sphereW) ∨
      (sphereW.model.boundary sphereW.Carrier = ∅ ∧
        ∃ g' : SmoothRiemannianMetric sphereW.model sphereW.Carrier,
          DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0) :=
  StrongCertificate.raw_or_aux_nonneg sphereW sphereStrongCertificate

/-! ## The branch taken by FC42's proof on this certificate -/

/-- The B1 test of FC42 fails: no vertex of the S³ certificate is a closed zero piece (`Z₋`, `Z₊`
are zero balls, `S` is slim). -/
theorem sphereStrongCertificate_vertex_ne_closedZero_E2E
    (k : Fin sphereStrongCertificate.1.vertexCount) (C : ClosedZeroPiece sphereW) :
    sphereStrongCertificate.1.vertex k ≠ .closedZero C := by
  intro h
  change Fin 3 at k
  fin_cases k <;> cases h

/-- The B2 test of the μ-recursion fails: the slim vertex is `S² × I`, not over the circle. -/
theorem sphereStrongCertificate_not_slimOverCircle_E2E :
    ¬ ∃ (k : Fin sphereStrongCertificate.1.vertexCount) (P : PieceEmbedding sphereW)
      (p : P.Piece → Circle) (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p)
      (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
      (fib : SlimFibre P p) (hcl : (𝓡∂ 3).boundary P.Piece = ∅),
      sphereStrongCertificate.1.vertex k = .slim P (.overCircle p hp hsub fib hcl) := by
  rintro ⟨k, P, p, hp, hsub, fib, hcl, h⟩
  change Fin 3 at k
  fin_cases k <;> cases h

/-- `μ > 0` (one sphere seam): the first step of the μ-recursion is the sphere step, not the torus
assembly with L1. -/
theorem sphereStrongCertificate_sphereMeasure_pos_E2E :
    0 < sphereStrongCertificate.1.sphereMeasure := by
  change 0 < 1 + _
  omega

/-- **The branch of FC42 on the S³ certificate: RAW**, by the μ-recursion with the production
packets (the branch FC42's proof takes when the B1 test fails). -/
theorem sphereStrongCertificate_raw_E2E : Nonempty (RawGraphPresentation sphereW) :=
  nonempty_rawGraphPresentation_of_rimProduct_of_steps
    exists_solidTorus_of_ballHandleCycle_of_rimProduct
    DecompositionCertificate.exists_sphereRecursionStep
    DecompositionCertificate.exists_internalSphereCut_puncturedRP3
    DecompositionCertificate.exists_internalSphereCut_sphereInterval
    exists_rawGraphPresentation_of_sphereCut_separating
    (fun W _ => exists_rawGraphPresentation_of_sphereCut_nonseparating W) sphereW
    sphereStrongCertificate.1 sphereStrongCertificate_vertex_ne_closedZero_E2E
    sphereStrongCertificate.2

/-- The route of FC42 on the S³ certificate in one statement: the B1 and B2 tests fail, `μ > 0`,
and the outcome is the raw disjunct. -/
theorem sphereStrongCertificate_fc42_route_E2E :
    (¬ ∃ k C, sphereStrongCertificate.1.vertex k = .closedZero C) ∧
      0 < sphereStrongCertificate.1.sphereMeasure ∧ Nonempty (RawGraphPresentation sphereW) :=
  ⟨fun ⟨k, C, h⟩ => sphereStrongCertificate_vertex_ne_closedZero_E2E k C h,
    sphereStrongCertificate_sphereMeasure_pos_E2E, sphereStrongCertificate_raw_E2E⟩

/-! ## Consumers downstream -/

/-- The chapter-14 interface disjunction on S³, from the strong consumer. -/
theorem sphere_raw_or_closedGeometric_E2E :
    Nonempty (RawGraphPresentation sphereW) ∨
      (sphereW.model.boundary sphereW.Carrier = ∅ ∧
        ∃ G : GC.Geometry.GeometricStructure sphereW.model sphereW.Carrier,
          G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) :=
  DifferentialGeometry.Geometry.Collapse.raw_or_closedGeometric_of_raw_or_aux_nonneg sphereW
    sphereStrongCertificate_raw_or_aux_nonneg_E2E

/-- `S³` geometrizes, through the raw branch of FC42 on its strong certificate. -/
theorem sphere_geometrizes_E2E : Geometrizes standardThreeSphereLift.{0} := by
  obtain ⟨G⟩ := sphereStrongCertificate_raw_E2E
  exact geometrizes_of_rawGraphPresentation standardThreeSphereLift.{0} G

/-! ## Finding: the conclusion is known a priori for S³ -/

/-- The raw disjunct holds for S³ WITHOUT any certificate (the Clifford presentation): the
end-to-end run checks that the hypotheses of FC42 are satisfiable by a real two-handle certificate,
not that its conclusion carries information on this example. -/
theorem sphere_raw_clifford_E2E : Nonempty (RawGraphPresentation sphereW) :=
  ⟨standardThreeSphereLiftRawGraphPresentation.{0}⟩

end GC.GraphManifold.Assembly.FC39P0
