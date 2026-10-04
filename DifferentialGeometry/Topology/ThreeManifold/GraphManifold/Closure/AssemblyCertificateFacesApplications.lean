import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateFaces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateSides

/-!
# Consumers of the certificate's structural lemmas

Read-offs of FC40 and of the protection lemmas on an arbitrary `DecompositionCertificate W E`:

* every handle end disk lies on a sphere face (`faceModel_handleFace_eq_inl`): a partitioned torus face
  carries no end disk (FC40, `AssemblyCertificateFaces.lean`);
* a partitioned torus face lies in the circle region (`face_subset_region_of_torus`): it is one whole
  loop face, and `face_region_inter` puts loops in the region;
* the rounding support of every corner avoids every external collar and every whole torus seam
  collar (`disjoint_roundingSupport_externalCollar`, `disjoint_roundingSupport_torusSeamCollar`),
  and a `none` seam side meets no sphere surgery support.
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

/-- **Handle ends sit on sphere faces.** -/
theorem faceModel_handleFace_eq_inl (h : Fin D.handleCount) (b : Bool) :
    ∃ φ, D.faceModel (D.handleFace h b) = Sum.inl φ := by
  rcases hφ : D.faceModel (D.handleFace h b) with φ | φ
  · exact ⟨φ, rfl⟩
  · exact absurd rfl (D.handleFace_ne_of_torus (D.handleFace_kind h b) φ h b)

/-- **A partitioned torus face lies in the circle region.** -/
theorem face_subset_region_of_torus {f : Fin D.faceCount} (hf : D.faceKind f = .partitioned)
    (φ : D.face f ≃ₜ Circle × Circle) : D.face f ⊆ D.circ.region := by
  obtain ⟨j, hj, hface, -⟩ := D.exists_loop_eq_face_of_torus hf φ
  intro x hx
  have hloop : x ∈ D.face f ∩ D.circ.region := by
    rw [D.face_region_inter f hf]
    refine Or.inr (mem_iUnion₂.2 ⟨j, hj, ?_⟩)
    rwa [← hface]
  exact hloop.2

/-- The rounding support of a corner avoids every external collar. -/
theorem disjoint_roundingSupport_externalCollar (k : Fin D.circ.cornerCount) (i : Fin n) :
    Disjoint (D.circ.roundingSupport k) (E.collar i).target :=
  (D.disjoint_roundingSupport_externalCollarSet k).mono_right
    (subset_iUnion (fun i => (E.collar i).target) i)

/-- The rounding support of a corner avoids every whole torus seam collar. -/
theorem disjoint_roundingSupport_torusSeamCollar (k : Fin D.circ.cornerCount)
    (c : Fin D.torusSeamCount) :
    Disjoint (D.circ.roundingSupport k) (D.torusSeam c).collar.target :=
  (D.disjoint_roundingSupport_torusCollarSet k).mono_right
    (subset_iUnion (fun c => (D.torusSeam c).collar.target) c)

/-- The half collar of a `none` torus seam side meets no sphere surgery support: it lies in the
circle region, which the sphere seam collars avoid. -/
theorem halfCollar_disjoint_sphereSupport_of_none {c : Fin D.torusSeamCount} {b : Bool}
    (hc : D.torusSide c b = none) :
    Disjoint ((D.torusSeam c).collar '' signedHalfSource b) D.sphereSupport := by
  refine (D.disjoint_sphereSupport_region.symm).mono_left ?_
  rintro _ ⟨p, hp, rfl⟩
  exact D.collar_mem_region_of_torusSide_eq_none hc hp

end DecompositionCertificate

end GC.GraphManifold.Assembly
