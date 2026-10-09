import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateSphereFaces

/-!
# Consumer: FC40 on a partitioned sphere face

With the `hbase` input (`AssemblyCertificateSphereFaces.lean`) and the other FC40 inputs
(`AssemblyCertificateFaces.lean`), `Surface.disk_face_count_sphereTwo` applies to every partitioned
face of a `DecompositionCertificate` homeomorphic to `S²`: it carries exactly two handle end disks and
exactly one circle-region stratum (`card_faceStratum_eq_one_and_card_faceEnd_eq_two`); that stratum is
an arc (`loopOwner_ne_of_sphere`, `exists_unique_arc_of_sphere`), and the two end disks are the two
ends of that arc (`handleFace_eq_iff_of_sphere`).
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

/-- **FC40 on a partitioned sphere face.** Two handle end disks and one stratum. -/
theorem card_faceStratum_eq_one_and_card_faceEnd_eq_two {f : Fin D.faceCount}
    (hf : D.faceKind f = .partitioned) (φ : D.face f ≃ₜ SphereTwo) :
    Fintype.card (D.FaceStratum f) = 1 ∧ Fintype.card (D.FaceEnd f) = 2 :=
  Surface.disk_face_count_sphereTwo φ (D.faceDisk f) (D.faceStratumSet f) (D.isClosed_faceDisk f)
    (D.isClosed_faceStratumSet f) (D.faceStratumSet_nonempty f)
    (D.iUnion_faceDisk_union_iUnion_faceStratumSet hf) (D.pairwise_disjoint_faceDisk f)
    (D.pairwise_disjoint_faceStratumSet f) (D.faceSide f) (D.faceSide_eq_of_nonempty f)
    (D.card_filter_faceSide f) (D.faceStratum_base f)

theorem nonempty_faceEnd_of_sphere {f : Fin D.faceCount} (hf : D.faceKind f = .partitioned)
    (φ : D.face f ≃ₜ SphereTwo) : Nonempty (D.FaceEnd f) :=
  Fintype.card_pos_iff.1 ((D.card_faceStratum_eq_one_and_card_faceEnd_eq_two hf φ).2 ▸ two_pos)

theorem subsingleton_faceStratum_of_sphere {f : Fin D.faceCount}
    (hf : D.faceKind f = .partitioned) (φ : D.face f ≃ₜ SphereTwo) :
    Subsingleton (D.FaceStratum f) :=
  Fintype.card_le_one_iff_subsingleton.1
    (D.card_faceStratum_eq_one_and_card_faceEnd_eq_two hf φ).1.le

/-- A partitioned sphere face has no loop. -/
theorem loopOwner_ne_of_sphere {f : Fin D.faceCount} (hf : D.faceKind f = .partitioned)
    (φ : D.face f ≃ₜ SphereTwo) (l : Fin D.loopFaceCount) : D.loopOwner l ≠ f := fun hl => by
  obtain ⟨i⟩ := D.nonempty_faceEnd_of_sphere hf φ
  have := (D.subsingleton_faceStratum_of_sphere hf φ).elim (D.faceSide f i) (.inr ⟨l, hl⟩)
  exact Sum.inl_ne_inr this

/-- **A partitioned sphere face has exactly one arc.** -/
theorem exists_unique_arc_of_sphere {f : Fin D.faceCount} (hf : D.faceKind f = .partitioned)
    (φ : D.face f ≃ₜ SphereTwo) :
    ∃ j : Fin D.arcFaceCount, D.arcOwner j = f ∧
      ∀ j' : Fin D.arcFaceCount, D.arcOwner j' = f → j' = j := by
  obtain ⟨i⟩ := D.nonempty_faceEnd_of_sphere hf φ
  refine ⟨D.handleArc i.1.1 i.1.2, (D.handleArc_owner _ _).trans i.2, fun j' hj' => ?_⟩
  have := (D.subsingleton_faceStratum_of_sphere hf φ).elim (.inl ⟨j', hj'⟩) (D.faceSide f i)
  exact congrArg Subtype.val (Sum.inl_injective this)

/-- **The two end disks of a partitioned sphere face are the two ends of its arc.** -/
theorem handleFace_eq_iff_of_sphere {D : DecompositionCertificate W E} {f : Fin D.faceCount}
    (hf : D.faceKind f = .partitioned) (φ : D.face f ≃ₜ SphereTwo) {j : Fin D.arcFaceCount}
    (hj : D.arcOwner j = f) {h : Fin D.handleCount} {b : Bool} :
    D.handleFace h b = f ↔ D.handleArc h b = j := by
  constructor
  · intro hhb
    have := (D.subsingleton_faceStratum_of_sphere hf φ).elim (D.faceSide f ⟨(h, b), hhb⟩)
      (.inl ⟨j, hj⟩)
    exact congrArg Subtype.val (Sum.inl_injective this)
  · intro hhb
    rw [← D.handleArc_owner, hhb, hj]

end DecompositionCertificate

end GC.GraphManifold.Assembly
