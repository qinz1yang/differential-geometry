import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.DoublePunctured
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.DoubleCylinderMappingTorus
import DifferentialGeometry.Topology.ThreeManifold.SphereMappingTorusTrivialization
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.QuotientTransport

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

def sphereSelfAttachmentMonodromy (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2 :=
  (sphereAntipodalDiffeomorph (E := E3) (n := 2)).trans a.symm

abbrev SphereSelfAttachment (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) :=
  SelfAttachment.Quotient (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P)
    (stereographicSmallBallChart_disjoint P) a.toHomeomorph

def doubleCylinderSphereSelfAttachmentHomeomorph (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) :
    DoubleCylinder.Space (sphereSelfAttachmentMonodromy a) ≃ₜ SphereSelfAttachment P a := by
  apply adjunctionSpaceHomeomorphOfHomeomorph
    SelfAttachment.boundaryInclusion (DoubleCylinder.attachingMap (sphereSelfAttachmentMonodromy a))
    SelfAttachment.boundaryInclusion
    (SelfAttachment.attachingMap (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P)
      (stereographicSmallBallChart_disjoint P) a.toHomeomorph)
    (Homeomorph.refl _) (Homeomorph.refl _) (sphereDoublePuncturedHomeomorph P)
  · intro q
    rfl
  · rintro ⟨b, z⟩
    cases b
    · apply Subtype.ext
      exact sphereDoublePuncturedHomeomorph_lower P z
    · apply Subtype.ext
      change (sphereDoublePuncturedHomeomorph P
        ((sphereSelfAttachmentMonodromy a).symm z, ⟨1, by norm_num⟩)).val =
          (oppositeStereographicSmallBallChart P).chart (a z).val
      rw [sphereDoublePuncturedHomeomorph_upper]
      change (oppositeStereographicSmallBallChart P).chart (-(-(a z))).val = _
      rw [neg_neg]

theorem doubleCylinderSphereSelfAttachmentHomeomorph_core
    (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (p : DoubleCylinder.Cylinder) :
    doubleCylinderSphereSelfAttachmentHomeomorph P a
      (DoubleCylinder.core (sphereSelfAttachmentMonodromy a) p) =
        SelfAttachment.coreInclusion (stereographicSmallBallChart P)
          (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P)
          a.toHomeomorph (sphereDoublePuncturedHomeomorph P p) := rfl

theorem doubleCylinderSphereSelfAttachmentHomeomorph_band
    (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (p : DoubleCylinder.Cylinder) :
    doubleCylinderSphereSelfAttachmentHomeomorph P a
      (DoubleCylinder.band (sphereSelfAttachmentMonodromy a) p) =
        SelfAttachment.bandInclusion (stereographicSmallBallChart P)
          (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P)
          a.toHomeomorph p := rfl

def sphereSelfAttachmentMappingTorusHomeomorph (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) :
    SphereSelfAttachment P a ≃ₜ SphereMappingTorus (sphereSelfAttachmentMonodromy a) :=
  (doubleCylinderSphereSelfAttachmentHomeomorph P a).symm.trans
    (DoubleCylinder.mappingTorusHomeomorph (sphereSelfAttachmentMonodromy a))

theorem sphereSelfAttachmentMappingTorusHomeomorph_core
    (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (p : DoubleCylinder.Cylinder) :
    sphereSelfAttachmentMappingTorusHomeomorph P a
      (SelfAttachment.coreInclusion (stereographicSmallBallChart P)
        (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P)
        a.toHomeomorph (sphereDoublePuncturedHomeomorph P p)) =
      DoubleCylinder.coreToMappingTorus (sphereSelfAttachmentMonodromy a) p := by
  rw [← doubleCylinderSphereSelfAttachmentHomeomorph_core]
  rw [sphereSelfAttachmentMappingTorusHomeomorph, Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply]
  rfl

theorem sphereSelfAttachmentMappingTorusHomeomorph_band
    (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (p : DoubleCylinder.Cylinder) :
    sphereSelfAttachmentMappingTorusHomeomorph P a
      (SelfAttachment.bandInclusion (stereographicSmallBallChart P)
        (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P)
        a.toHomeomorph p) =
      DoubleCylinder.bandToMappingTorus (sphereSelfAttachmentMonodromy a) p := by
  rw [← doubleCylinderSphereSelfAttachmentHomeomorph_band]
  rw [sphereSelfAttachmentMappingTorusHomeomorph, Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply]
  rfl

end DifferentialGeometry.Topology.Manifold
