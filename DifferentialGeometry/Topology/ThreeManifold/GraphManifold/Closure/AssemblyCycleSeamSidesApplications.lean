import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleSeamSides
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCyclePartitionApplications

/-!
# Consumers of packet G3 (seam sides, faces, bad vertices)

* `nonempty_cyclePartition_of_badVertexCount_eq_zero`: the terminal B5 feeds the cycle partition
  (H2): without sphere seams and without bad vertices the ball–handle multigraph has a complete
  cycle partition. (The existence of a cycle partition by itself does not encode the termination
  of the FC42 normalization: it says nothing about the vertices that are neither balls nor handle
  ends, review 42 §2.3.)
* `existsUnique_face_of_isBall`: a ball vertex owns exactly one face (no sphere-seam hypothesis:
  `face_eq_boundaryImage_of_isPreconnected` and `face_disjoint_of_faceOwner_eq`).
* `torusSide_ne_of_false`: the side theorem with the roles of the two sides exchanged.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **Terminal B5 → H2.** Without sphere seams and without bad vertices, the certificate has a
complete cycle partition. -/
theorem nonempty_cyclePartition_of_badVertexCount_eq_zero (hsph : D.sphereSeamCount = 0)
    (hbad : D.badVertexCount = 0) : Nonempty D.CyclePartition :=
  D.nonempty_cyclePartition hsph fun f hf hS =>
    D.partitionedSphereFace_ball_of_badVertexCount_eq_zero hbad f hf hS

/-- A ball vertex owns exactly one face. -/
theorem existsUnique_face_of_isBall {k : Fin D.vertexCount} (hk : (D.vertex k).IsBall) :
    ∃! f, D.faceOwner f = k := by
  obtain ⟨x, hx⟩ := hk.boundaryImage_nonempty
  rw [← D.face_exhausted k] at hx
  obtain ⟨f, hx⟩ := mem_iUnion.mp hx
  obtain ⟨hf, -⟩ := mem_iUnion.mp hx
  refine ⟨f, hf, fun f' hf' => ?_⟩
  by_contra hne
  have hpre := hk.isConnected_boundaryImage.isPreconnected
  have hdis := D.face_disjoint_of_faceOwner_eq hne (hf'.trans hf.symm)
  rw [D.face_eq_boundaryImage_of_isPreconnected hpre f' hf',
    D.face_eq_boundaryImage_of_isPreconnected hpre f hf, disjoint_self, bot_eq_empty] at hdis
  exact hk.boundaryImage_nonempty.ne_empty hdis

/-- The torus side theorem with the two sides exchanged. -/
theorem torusSide_ne_of_false (c : Fin D.torusSeamCount) (k : Fin D.vertexCount)
    (hk : D.torusSide c false = some k) : D.torusSide c true ≠ some k := fun h =>
  D.torusSide_ne c k h hk

end DecompositionCertificate

end GC.GraphManifold.Assembly
