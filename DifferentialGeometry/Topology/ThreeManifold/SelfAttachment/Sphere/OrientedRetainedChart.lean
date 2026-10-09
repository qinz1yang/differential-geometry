import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.RetainedChart
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Orientation
import DifferentialGeometry.Topology.Manifold.OrientedBallChartOpenImage

set_option autoImplicit false
noncomputable section
open Set Function
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
  (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
  (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1))

theorem exists_sphereProduct_orientation_correction :
    ∃ r : sphereTwoTimesCircleLift.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ sphereTwoTimesCircleLift.Carrier,
      ∀ x : sphereDoublePuncturedInteriorImage P D hI,
        Orientation.map (Fin 3)
          ((DifferentialGeometry.isLocalDiffeomorph_comp r.isLocalDiffeomorph
            (sphereSelfAttachmentCoreToSphereProduct_isLocalDiffeomorph
              P a D hI h0 h1 J hJtarget hJ hJi)).mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
          (standardThreeSphere.orientation.orientation x.val) = sphereTwoTimesCircleLift.orientation.orientation
            (r (sphereSelfAttachmentCoreToSphereProduct P a D hI h0 h1 J hJtarget x)) := by
  let f := sphereSelfAttachmentCoreToSphereProduct P a D hI h0 h1 J hJtarget
  let hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f :=
    sphereSelfAttachmentCoreToSphereProduct_isLocalDiffeomorph P a D hI h0 h1 J hJtarget hJ hJi
  let _ := connectedSpace_sphereDoublePuncturedInteriorImage P D hI
  let o := standardThreeSphere.orientation.restrictOpen (sphereDoublePuncturedInteriorImage P D hI)
  rcases localDiffeomorph_orientation_dichotomy f hf
    (sphereSelfAttachmentCoreToSphereProduct_injective P a D hI h0 h1 J hJtarget) o
    sphereTwoTimesCircleLift.orientation with hp | hn
  · refine ⟨Diffeomorph.refl (𝓡 3) sphereTwoTimesCircleLift.Carrier ∞, ?_⟩
    exact localDiffeomorph_orientation_comp f hf o _ _ hp _
      (Diffeomorph.preservesOrientation_refl sphereTwoTimesCircleLift.orientation)
  · obtain ⟨r, hr⟩ := exists_orientationReversing_sphereTwoTimesCircleLift
    refine ⟨r, ?_⟩
    exact localDiffeomorph_orientation_comp f hf o sphereTwoTimesCircleLift.orientation.opposite
      sphereTwoTimesCircleLift.orientation hn r hr

include hJ hJi in
theorem exists_orientedBallChart_sphereProduct_of_retained_chart :
    ∃ r : sphereTwoTimesCircleLift.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ sphereTwoTimesCircleLift.Carrier,
      ∀ c : OrientedBallChart standardThreeSphere.toClosedOrientedManifold,
      (∀ x ∈ Metric.closedBall (0 : E3) 2,
        c.chart x ∉ (stereographicSmallBallChart P).chart '' Metric.closedBall 0 1 ∪
          (oppositeStereographicSmallBallChart P).chart '' Metric.closedBall 0 1) →
      ∃ c' : OrientedBallChart sphereTwoTimesCircleLift.toClosedOrientedManifold,
        ∀ x ∈ Metric.closedBall (0 : E3) 2,
          ∃ hx : c.chart x ∈ sphereDoublePuncturedInteriorImage P D hI,
            c'.chart x = r (sphereSelfAttachmentCoreToSphereProduct P a D hI h0 h1 J hJtarget ⟨c.chart x, hx⟩) := by
  obtain ⟨r, hr⟩ := exists_sphereProduct_orientation_correction P a D hI h0 h1 J hJtarget hJ hJi
  refine ⟨r, ?_⟩
  intro c havoid
  have hU : ∀ x ∈ Metric.closedBall (0 : E3) 2, c.chart x ∈ sphereDoublePuncturedInteriorImage P D hI := by
    intro x hx
    change c.chart x ∈ (sphereDoublePuncturedInteriorImage P D hI : Set S3)
    rw [sphereDoublePuncturedInteriorImage_eq P D hI h0 h1]
    exact havoid x hx
  let f := sphereSelfAttachmentCoreToSphereProduct P a D hI h0 h1 J hJtarget
  let hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f :=
    sphereSelfAttachmentCoreToSphereProduct_isLocalDiffeomorph P a D hI h0 h1 J hJtarget hJ hJi
  have hg : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (r ∘ f) :=
    DifferentialGeometry.isLocalDiffeomorph_comp r.isLocalDiffeomorph hf
  obtain ⟨c', hc'⟩ := c.exists_orientedBallChart_of_open_embedding
    (sphereDoublePuncturedInteriorImage P D hI) (r ∘ f) hg
    (r.injective.comp (sphereSelfAttachmentCoreToSphereProduct_injective P a D hI h0 h1 J hJtarget)) hr hU
  exact ⟨c', fun x hx => ⟨hU x hx, hc' x hx⟩⟩

end DifferentialGeometry.Topology.Manifold
