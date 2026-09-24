import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.Core
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.Orientation
import DifferentialGeometry.Topology.Manifold.BallChartOpenImage

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev S3 := Metric.sphere (0 : E4) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

variable (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
  (D : ℝ ≃ₘ[ℝ] ℝ) (hI : D '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1)
  (h0 : D 0 = 0) (h1 : D 1 = 1)
  (J : SphereMappingTorusIsotopy) (hJtarget : J.target = sphereSelfAttachmentMonodromy a)

theorem sphereSelfAttachmentCoreMap_injective : Injective (sphereSelfAttachmentCoreMap P a D hI) := by
  intro p q h
  obtain ⟨hp, hep⟩ := sphereSelfAttachmentCoreMap_eq P a D hI p
  obtain ⟨hq, heq⟩ := sphereSelfAttachmentCoreMap_eq P a D hI q
  rw [hep, heq] at h
  have hx := SelfAttachment.coreInclusion_injective (stereographicSmallBallChart P)
    (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P) a.toHomeomorph h
  exact Subtype.ext (congrArg (fun x : (stereographicSmallBallChart P).DoublePunctured
    (oppositeStereographicSmallBallChart P) => x.val) hx)

def sphereSelfAttachmentCoreToSphereProduct :
    sphereDoublePuncturedInteriorImage P D hI → sphereTwoTimesCircleLift.Carrier := by
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  let F : Diffeomorph IC ((𝓡 2).prod (𝓡 1)) (SphereSelfAttachment P a) SphereTwoTimesCircle ∞ :=
    sphereSelfAttachmentDiffeomorphSphereTwoTimesCircle P a D hI h0 h1 J hJtarget
  exact fun x => sphereTwoTimesCircleModelCopy.equiv (F (sphereSelfAttachmentCoreMap P a D hI x))

theorem sphereSelfAttachmentCoreToSphereProduct_isLocalDiffeomorph
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1)) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (sphereSelfAttachmentCoreToSphereProduct P a D hI h0 h1 J hJtarget) := by
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  let F : Diffeomorph IC ((𝓡 2).prod (𝓡 1)) (SphereSelfAttachment P a) SphereTwoTimesCircle ∞ :=
    sphereSelfAttachmentDiffeomorphSphereTwoTimesCircle P a D hI h0 h1 J hJtarget
  exact DifferentialGeometry.isLocalDiffeomorph_comp sphereTwoTimesCircleModelCopy.equiv.isLocalDiffeomorph
    (DifferentialGeometry.isLocalDiffeomorph_comp F.isLocalDiffeomorph
      (sphereSelfAttachmentCoreMap_isLocalDiffeomorph P a D hI h0 h1 J hJtarget hJ hJi))

theorem sphereSelfAttachmentCoreToSphereProduct_injective :
    Injective (sphereSelfAttachmentCoreToSphereProduct P a D hI h0 h1 J hJtarget) := by
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  let F : Diffeomorph IC ((𝓡 2).prod (𝓡 1)) (SphereSelfAttachment P a) SphereTwoTimesCircle ∞ :=
    sphereSelfAttachmentDiffeomorphSphereTwoTimesCircle P a D hI h0 h1 J hJtarget
  exact sphereTwoTimesCircleModelCopy.equiv.injective.comp
    (F.injective.comp (sphereSelfAttachmentCoreMap_injective P a D hI))

theorem exists_ballChart_sphereProduct_of_retained_chart
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1))
    (c : BallChart 3 (𝓡 3) S3)
    (havoid : ∀ x ∈ Metric.closedBall (0 : E3) 2,
      c.chart x ∉ (stereographicSmallBallChart P).chart '' Metric.closedBall 0 1 ∪
        (oppositeStereographicSmallBallChart P).chart '' Metric.closedBall 0 1) :
    ∃ c' : BallChart 3 (𝓡 3) sphereTwoTimesCircleLift.Carrier,
      ∀ x ∈ Metric.closedBall (0 : E3) 2,
        ∃ hx : c.chart x ∈ sphereDoublePuncturedInteriorImage P D hI,
          c'.chart x = sphereSelfAttachmentCoreToSphereProduct P a D hI h0 h1 J hJtarget ⟨c.chart x, hx⟩ := by
  have hU : ∀ x ∈ Metric.closedBall (0 : E3) 2,
      c.chart x ∈ sphereDoublePuncturedInteriorImage P D hI := by
    intro x hx
    change c.chart x ∈ (sphereDoublePuncturedInteriorImage P D hI : Set S3)
    rw [sphereDoublePuncturedInteriorImage_eq P D hI h0 h1]
    exact havoid x hx
  obtain ⟨c', _, _, hc'⟩ := c.exists_ballChart_of_open_embedding
    (sphereDoublePuncturedInteriorImage P D hI)
    (sphereSelfAttachmentCoreToSphereProduct P a D hI h0 h1 J hJtarget)
    (sphereSelfAttachmentCoreToSphereProduct_isLocalDiffeomorph P a D hI h0 h1 J hJtarget hJ hJi)
    (sphereSelfAttachmentCoreToSphereProduct_injective P a D hI h0 h1 J hJtarget) hU
  exact ⟨c', fun x hx => ⟨hU x hx, hc' x hx⟩⟩

end DifferentialGeometry.Topology.Manifold
