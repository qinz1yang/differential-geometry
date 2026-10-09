import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateFaces

/-!
# The FC39 certificate: the base projection of a loop stratum (FC40 `hbase`)

FC40 on a sphere face (`Surface.disk_face_count_sphereTwo`, `DiskFaceRecognition.lean:81`) needs, for
every stratum without disks, an open continuous map to the circle (`hbase`). In the certificate the
strata without disks are the loop faces, and the map is the circle-region projection followed by the
inverse of the loop base embedding:

* `CircleRegion.isOpenMap_proj`: the projection of the circle region is open (locally it is the first
  factor of a trivialization);
* `DecompositionCertificate.exists_loopProjection`: the loop face `loopFace l`, read inside its owner
  face, maps continuously and openly onto the circle — the restriction of the open projection to the
  full preimage of the embedded base circle `range (loopBase l)`, then that circle's inverse chart;
* `DecompositionCertificate.faceStratum_base`: the `hbase` input of FC40 on any face.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace CircleRegion

variable {W : CompactCarrier.{u}}

/-- The projection of a circle region is an open map: on the trivialization domain over each base
neighbourhood it is the first factor of a homeomorphism onto `neighbourhood × Circle`. -/
theorem isOpenMap_proj (R : CircleRegion W) : IsOpenMap R.proj := by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨a, ha, rfl⟩
  have haV : a ∈ TopologicalSpace.Opens.comap R.proj (R.neighborhood (R.proj a)) := by
    rw [TopologicalSpace.Opens.mem_comap]
    exact R.mem_neighborhood _
  have hU' : IsOpen (Subtype.val ⁻¹' U :
      Set (TopologicalSpace.Opens.comap R.proj (R.neighborhood (R.proj a)))) :=
    hU.preimage continuous_subtype_val
  have h1 := (R.trivialization (R.proj a)).toHomeomorph.isOpenMap _ hU'
  have h2 := isOpenMap_fst _ h1
  have h3 := (R.neighborhood (R.proj a)).isOpen.isOpenMap_subtype_val _ h2
  refine ⟨_, ?_, h3, ?_⟩
  · rintro _ ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
    exact ⟨v.val, hv, (R.projection_trivialization _ v).symm⟩
  · exact ⟨_, ⟨_, ⟨⟨a, haV⟩, ha, rfl⟩, rfl⟩, R.projection_trivialization _ _⟩

end CircleRegion

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **The base projection of a loop stratum.** Inside its owner face, the loop face `loopFace l`
maps continuously and openly onto the circle. -/
theorem exists_loopProjection (f : Fin D.faceCount)
    (l : {l : Fin D.loopFaceCount // D.loopOwner l = f}) :
    ∃ p : D.faceStratumSet f (.inr l) → Circle, Continuous p ∧ IsOpenMap p := by
  have hemb := (D.loopBase_embedding l.1).isEmbedding
  have h₁ : IsEmbedding fun y : D.faceStratumSet f (.inr l) => y.1.1 :=
    IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have h₂ : IsEmbedding fun z : D.circ.proj ⁻¹' range (D.loopBase l.1) => z.1.1 :=
    IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have hr : (range fun y : D.faceStratumSet f (.inr l) => y.1.1) =
      range fun z : D.circ.proj ⁻¹' range (D.loopBase l.1) => z.1.1 := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have hy : y.1.1 ∈ D.loopFace l.1 := y.2
      rw [D.loopFace_eq] at hy
      obtain ⟨w, hw, hwx⟩ := hy
      exact ⟨⟨w, hw⟩, hwx⟩
    · rintro ⟨z, rfl⟩
      have hz : z.1.1 ∈ D.loopFace l.1 := by
        rw [D.loopFace_eq]
        exact ⟨z.1, z.2, rfl⟩
      have hzf : z.1.1 ∈ D.face f := by
        have := D.loopFace_subset_face l.1 hz
        rwa [l.2] at this
      exact ⟨⟨⟨z.1.1, hzf⟩, hz⟩, rfl⟩
  let ψ : D.faceStratumSet f (.inr l) ≃ₜ D.circ.proj ⁻¹' range (D.loopBase l.1) :=
    (h₁.toHomeomorph.trans (Homeomorph.setCongr hr)).trans h₂.toHomeomorph.symm
  refine ⟨fun y => hemb.toHomeomorph.symm
    ((range (D.loopBase l.1)).restrictPreimage D.circ.proj (ψ y)), ?_, ?_⟩
  · exact hemb.toHomeomorph.symm.continuous.comp
      (D.circ.proj.continuous.restrictPreimage.comp ψ.continuous)
  · exact hemb.toHomeomorph.symm.isOpenMap.comp
      ((D.circ.isOpenMap_proj.restrictPreimage _).comp ψ.isOpenMap)

/-- FC40 `hbase`: every stratum without disks (a loop) has an open continuous map to the circle. -/
theorem faceStratum_base (f : Fin D.faceCount) (j : D.FaceStratum f)
    (hj : (Finset.univ.filter fun i => D.faceSide f i = j).card = 0) :
    ∃ p : D.faceStratumSet f j → Circle, Continuous p ∧ IsOpenMap p := by
  rcases j with j | l
  · rw [D.card_filter_faceSide_inl] at hj
    exact absurd hj (by norm_num)
  · exact D.exists_loopProjection f l

end DecompositionCertificate

end GC.GraphManifold.Assembly
