import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42FinalApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1Cycle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecStep
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormSphereCutProjective
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelSepApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelNonsepApplications

/-!
# FC42 packet F1: the final theorem (lane ASM-F1 template; swap module)

FC42 in form (b) (lead decision M1), unconditional: the plain hypotheses of
`exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct_of_steps` are discharged by
L1 `exists_solidTorus_of_ballHandleCycle_of_rimProduct`, S5
`DecompositionCertificate.exists_sphereRecursionStep`, N2 / N3
`DecompositionCertificate.exists_internalSphereCut_puncturedRP3` / `…_sphereInterval`, A4 / A3
`exists_rawGraphPresentation_of_sphereCut_separating` / `…_nonseparating` (the production names of
FC42Dry `dry_L2_separating` / `dry_L2_nonseparating`; A3 without its unused connectedness instance,
re-bound by a lambda). Swap module prepared by lane ASM-NRM4 from the ASM-F1 template.

* `DecompositionCertificate.exists_sphereStep` — the N4 (b) frozen text (F1-owned, decision M2);
* `exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct` — FC42, form (b);
* `exists_graph_threshold_disj_of_rimProduct_bindings_fc42` — the static threshold, form (b).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **N4 (b), frozen text** (`build-logs/scratch/ASM-NRM/Targets.lean:401`): the sphere step of
FC42. -/
theorem exists_sphereStep [ConnectedSpace W.Carrier] (hnz : ∀ k C, D.vertex k ≠ .closedZero C)
    (hμ : 0 < D.sphereMeasure) :
    ∃ (S : SphereSeam W) (X : SphereCutCapped W S E) (DQ : X.Q.Components), ∀ i : Fin DQ.count,
      Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) ∨
      Nonempty ((GC.Topology.componentCarrier X.Q DQ i).Carrier ≃ₘ⟮
        (GC.Topology.componentCarrier X.Q DQ i).model, 𝓡 3⟯ projectiveThreeSpaceLift.{u}.Carrier) ∨
      ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i)
          (X.componentTori DQ i),
        D'.sphereMeasure < D.sphereMeasure ∧ (∀ k C, D'.vertex k ≠ .closedZero C) ∧
        (D.RimProduct → D'.RimProduct) :=
  D.exists_sphereStep_of_steps hμ (D.exists_sphereRecursionStep hnz)
    (fun hσ _ hk _ _ _ _ _ hv => D.exists_internalSphereCut_puncturedRP3 hnz hσ hk hv)
    (fun hσ _ hk _ _ hv => D.exists_internalSphereCut_sphereInterval hnz hσ hk hv)

end DecompositionCertificate

/-- **FC42, form (b)**: a certificate with the rim-product clause gives a raw presentation, or the
carrier is closed with an auxiliary `sec ≥ 0` metric. -/
theorem exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ} {E : BoundaryTori W n}
    (D : DecompositionCertificate W E) (hprod : D.RimProduct) :
    Nonempty (RawGraphPresentation W) ∨
      (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
        DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0) :=
  exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct_of_steps
    exists_solidTorus_of_ballHandleCycle_of_rimProduct
    DecompositionCertificate.exists_sphereRecursionStep
    DecompositionCertificate.exists_internalSphereCut_puncturedRP3
    DecompositionCertificate.exists_internalSphereCut_sphereInterval
    exists_rawGraphPresentation_of_sphereCut_separating
    (fun W _ => exists_rawGraphPresentation_of_sphereCut_nonseparating W) W D hprod

/-- **The static threshold in V3 form, form (b)**, from the two bindings producing certificates with
the rim-product clause. -/
theorem exists_graph_threshold_disj_of_rimProduct_bindings_fc42 (K : ℕ) (A : ℝ → ℝ)
    (closedBinding : ∃ D : ClosedEarlyData, ∃ T : ClosedThresholds D,
      ∀ (R : ClosedRegister D T) (n : ℕ), max 2 R.later.tail ≤ n →
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier),
          (∀ p, curvatureRadius g p ≠ ⊤) →
          closedCollapseHypotheses W g K A (closedCounterexampleRatio n) →
          ∃ Dc : ClosedDecompositionCertificate W, Dc.cert.RimProduct)
    (boundaryBinding : ∃ D : BoundaryEarlyData, ∃ T : BoundaryThresholds D,
      ∀ (R : BoundaryRegister D T) (n : ℕ), max 2 R.tail ≤ n →
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier)
          (B : NearlyCuspidalBoundary W g K (boundaryCounterexampleRatio D.δStar n)),
          boundaryVolumeCollapsed W g (boundaryCounterexampleRatio D.δStar n) →
          curvatureDerivativesControlled g K A (boundaryCounterexampleRatio D.δStar n) →
          ∃ E : BoundaryTori W B.count,
            (∃ Dc : DecompositionCertificate W E, Dc.RimProduct) ∧
            ∀ i, Set.range (E.torusMap i) = B.component i) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        staticCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            (W.model.boundary W.Carrier = ∅ ∧
              ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
                G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) :=
  exists_graph_threshold_disj_of_rimProduct_bindings K A closedBinding boundaryBinding
    fun W _ _ _ D hp =>
      exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct W D hp

end GC.GraphManifold.Assembly
