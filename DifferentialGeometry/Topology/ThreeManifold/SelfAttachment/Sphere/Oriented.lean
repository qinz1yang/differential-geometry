import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.StandardModel

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

private theorem exists_orientation_diffeomorph_pullback {M N : Type*}
    [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold (𝓡 3) ∞ N]
    (F : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) (oN : ManifoldOrientation (𝓡 3) N 3) :
    ∃ oM : ManifoldOrientation (𝓡 3) M 3, F.preservesOrientation oM oN := by
  let so := smoothOrientationOfManifoldOrientation (𝓡 3)
    (OrientationAssembly.reindexManifoldOrientation (𝓡 3) (finCongr oN.dimension_eq.symm) oN)
  let hbij : ∀ x, Bijective (mfderiv (𝓡 3) (𝓡 3) F x) :=
    fun x => (F.mfderivToContinuousLinearEquiv (by simp) x).bijective
  let po := pullbackSmoothOrientation (𝓡 3) (𝓡 3) F F.contMDiff hbij so
  obtain ⟨O, hO⟩ := exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 3) po
  let oM := OrientationAssembly.reindexManifoldOrientation (𝓡 3) (finCongr (by simp : Module.finrank ℝ E3 = 3)) O
  refine ⟨oM, ?_⟩
  apply Diffeomorph.preservesOrientation_of_pullbackSmoothOrientation F F.contMDiff hbij so oM oN
  · intro y
    rfl
  · intro x
    change Orientation.reindex ℝ E3 _ (O.orientation x) = _
    rw [hO]

variable (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
  (D : ℝ ≃ₘ[ℝ] ℝ) (hI : D '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1)
  (h0 : D 0 = 0) (h1 : D 1 = 1)
  (J : SphereMappingTorusIsotopy) (hJtarget : J.target = sphereSelfAttachmentMonodromy a)
  (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
  (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1))

theorem exists_sphereSelfAttachment_oriented_diffeomorph :
    let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
    let _ := sphereSelfAttachmentStandard_isManifold P a D hI h0 h1 J hJtarget
    let hc : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (sphereSelfAttachmentCoreMap P a D hI) :=
      sphereSelfAttachmentStandard_core_isLocalDiffeomorph P a D hI h0 h1 J hJtarget hJ hJi
    ∃ r : sphereTwoTimesCircleLift.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ sphereTwoTimesCircleLift.Carrier,
    ∃ O : ManifoldOrientation (𝓡 3) (SphereSelfAttachment P a) 3,
      (∀ x, Orientation.map (Fin 3) (hc.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
        (standardThreeSphere.orientation.orientation x.val) = O.orientation (sphereSelfAttachmentCoreMap P a D hI x)) ∧
      ∃ F : SphereSelfAttachment P a ≃ₘ⟮𝓡 3, 𝓡 3⟯ sphereTwoTimesCircleLift.Carrier,
        F.preservesOrientation O sphereTwoTimesCircleLift.orientation ∧
        (∀ q, F q = r (sphereSelfAttachmentStandardHomeomorph P a D hI h0 h1 J hJtarget q)) ∧
        ∀ c : OrientedBallChart standardThreeSphere.toClosedOrientedManifold,
          (∀ x ∈ Metric.closedBall (0 : E3) 2,
            c.chart x ∉ (stereographicSmallBallChart P).chart '' Metric.closedBall 0 1 ∪
              (oppositeStereographicSmallBallChart P).chart '' Metric.closedBall 0 1) →
          ∃ c' : OrientedBallChart sphereTwoTimesCircleLift.toClosedOrientedManifold,
            ∀ x ∈ Metric.closedBall (0 : E3) 2,
              ∃ hx : c.chart x ∈ sphereDoublePuncturedInteriorImage P D hI,
                c'.chart x = F (sphereSelfAttachmentCoreMap P a D hI ⟨c.chart x, hx⟩) := by
  let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
  let _ := sphereSelfAttachmentStandard_isManifold P a D hI h0 h1 J hJtarget
  let hc : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (sphereSelfAttachmentCoreMap P a D hI) :=
    sphereSelfAttachmentStandard_core_isLocalDiffeomorph P a D hI h0 h1 J hJtarget hJ hJi
  obtain ⟨r, hr⟩ := exists_sphereProduct_orientation_correction P a D hI h0 h1 J hJtarget hJ hJi
  let G : SphereSelfAttachment P a ≃ₘ⟮𝓡 3, 𝓡 3⟯ sphereTwoTimesCircleLift.Carrier :=
    sphereSelfAttachmentStandardDiffeomorph P a D hI h0 h1 J hJtarget
  let F := G.trans r
  obtain ⟨O, hF⟩ := exists_orientation_diffeomorph_pullback F sphereTwoTimesCircleLift.orientation
  have hcore : ∀ x, Orientation.map (Fin 3) (hc.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (standardThreeSphere.orientation.orientation x.val) = O.orientation (sphereSelfAttachmentCoreMap P a D hI x) := by
    intro x
    let L := (F.mfderivToContinuousLinearEquiv (by simp) (sphereSelfAttachmentCoreMap P a D hI x)).toLinearEquiv
    apply (Orientation.map (Fin 3) L).injective
    rw [show Orientation.map (Fin 3) L (O.orientation (sphereSelfAttachmentCoreMap P a D hI x)) =
      sphereTwoTimesCircleLift.orientation.orientation (F (sphereSelfAttachmentCoreMap P a D hI x)) from hF _]
    have h := hr x
    have heq : ((DifferentialGeometry.isLocalDiffeomorph_comp r.isLocalDiffeomorph
        (sphereSelfAttachmentCoreToSphereProduct_isLocalDiffeomorph
          P a D hI h0 h1 J hJtarget hJ hJi)).mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv =
        (hc.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.trans L := by
      apply LinearEquiv.ext
      intro v
      change mfderiv (𝓡 3) (𝓡 3)
        (r ∘ sphereSelfAttachmentCoreToSphereProduct P a D hI h0 h1 J hJtarget) x v =
        mfderiv (𝓡 3) (𝓡 3) F (sphereSelfAttachmentCoreMap P a D hI x)
          (mfderiv (𝓡 3) (𝓡 3) (sphereSelfAttachmentCoreMap P a D hI) x v)
      have he : r ∘ sphereSelfAttachmentCoreToSphereProduct P a D hI h0 h1 J hJtarget =
          F ∘ sphereSelfAttachmentCoreMap P a D hI := rfl
      rw [he]
      exact mfderiv_comp_apply x (F.mdifferentiable (by simp) _) (hc.mdifferentiable (by simp) _) v
    rw [heq] at h
    erw [← DifferentialGeometry.VectorBundle.map_orientation_trans_between] at h
    exact h
  refine ⟨r, O, hcore, F, hF, fun _ => rfl, ?_⟩
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
