import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.Oriented

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

abbrev antipodalAttachment : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2 :=
  sphereAntipodalDiffeomorph (E := E3) (n := 2)

theorem sphereSelfAttachmentMonodromy_antipodal :
    sphereSelfAttachmentMonodromy antipodalAttachment = Diffeomorph.refl (𝓡 2) S2 ∞ := by
  apply Diffeomorph.ext
  intro z
  exact neg_neg z

theorem sphereMappingTorusIsotopyRefl_target :
    sphereMappingTorusIsotopyRefl.target = sphereSelfAttachmentMonodromy antipodalAttachment :=
  sphereSelfAttachmentMonodromy_antipodal.symm

variable (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
  (D : ℝ ≃ₘ[ℝ] ℝ) (hI : D '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1)
  (h0 : D 0 = 0) (h1 : D 1 = 1)
  (J : SphereMappingTorusIsotopy) (hJtarget : J.target = sphereSelfAttachmentMonodromy a)

def sphereSelfAttachmentManifold
    (O : let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
      ManifoldOrientation (𝓡 3) (SphereSelfAttachment P a) 3) : ConnectedClosedOrientedManifold 3 := by
  let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
  let H := sphereSelfAttachmentStandardHomeomorph P a D hI h0 h1 J hJtarget
  exact
    { Carrier := SphereSelfAttachment P a
      topology := inferInstance
      charts := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
      smooth := sphereSelfAttachmentStandard_isManifold P a D hI h0 h1 J hJtarget
      hausdorff := inferInstance
      compact := inferInstance
      orientation := O
      connected := H.connectedSpace_iff.mpr inferInstance }

omit a D hI h0 h1 J hJtarget in
theorem exists_antipodalSelfAttachment_oriented_model :
    ∃ (D : ℝ ≃ₘ[ℝ] ℝ) (hI : D '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1)
      (h0 : D 0 = 0) (h1 : D 1 = 1),
      (D : ℝ → ℝ) =ᶠ[𝓝 0] (fun t => t / 15) ∧
      (D : ℝ → ℝ) =ᶠ[𝓝 1] (fun t => (16 / (2 - t) - 1) / 15) ∧
      let _ := sphereSelfAttachmentStandardCharts P antipodalAttachment D hI h0 h1
        sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
      let hc : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (sphereSelfAttachmentCoreMap P antipodalAttachment D hI) :=
        sphereSelfAttachmentStandard_core_isLocalDiffeomorph P antipodalAttachment D hI h0 h1
          sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target contMDiff_fst contMDiff_fst
      ∃ O : ManifoldOrientation (𝓡 3) (SphereSelfAttachment P antipodalAttachment) 3,
        (∀ x, Orientation.map (Fin 3) (hc.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
          (standardThreeSphere.orientation.orientation x.val) =
          O.orientation (sphereSelfAttachmentCoreMap P antipodalAttachment D hI x)) ∧
        ∃ F : ClosedOrientedManifold.OrientedDiffeomorph
          (sphereSelfAttachmentManifold P antipodalAttachment D hI h0 h1 sphereMappingTorusIsotopyRefl
            sphereMappingTorusIsotopyRefl_target O).toClosedOrientedManifold sphereTwoTimesCircleLift.toClosedOrientedManifold,
          ∀ c : OrientedBallChart standardThreeSphere.toClosedOrientedManifold,
            (∀ x ∈ Metric.closedBall (0 : E3) 2,
              c.chart x ∉ (stereographicSmallBallChart P).chart '' Metric.closedBall 0 1 ∪
                (oppositeStereographicSmallBallChart P).chart '' Metric.closedBall 0 1) →
            ∃ c' : OrientedBallChart sphereTwoTimesCircleLift.toClosedOrientedManifold,
              ∀ x ∈ Metric.closedBall (0 : E3) 2,
                ∃ hx : c.chart x ∈ sphereDoublePuncturedInteriorImage P D hI,
                  c'.chart x = F.val (sphereSelfAttachmentCoreMap P antipodalAttachment D hI ⟨c.chart x, hx⟩) := by
  obtain ⟨D, _, hI, hlow, hupp⟩ := exists_stereographic_cylinder_reparametrization
  have h0 : D 0 = 0 := by simpa using hlow.self_of_nhds
  have h1 : D 1 = 1 := by
    have h := hupp.self_of_nhds
    norm_num at h
    exact h
  refine ⟨D, hI, h0, h1, hlow, hupp, ?_⟩
  let _ := sphereSelfAttachmentStandardCharts P antipodalAttachment D hI h0 h1
    sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
  obtain ⟨_, O, hcore, F, hF, _, hmark⟩ := exists_sphereSelfAttachment_oriented_diffeomorph
    P antipodalAttachment D hI h0 h1 sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
    contMDiff_fst contMDiff_fst
  exact ⟨O, hcore, ⟨F, hF⟩, hmark⟩

end DifferentialGeometry.Topology.Manifold
