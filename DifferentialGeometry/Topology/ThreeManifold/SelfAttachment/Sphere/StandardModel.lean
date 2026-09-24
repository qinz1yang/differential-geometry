import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.OrientedRetainedChart

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

def sphereSelfAttachmentStandardHomeomorph :
    SphereSelfAttachment P a ≃ₜ sphereTwoTimesCircleLift.Carrier := by
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  let F : Diffeomorph IC ((𝓡 2).prod (𝓡 1)) (SphereSelfAttachment P a) SphereTwoTimesCircle ∞ :=
    sphereSelfAttachmentDiffeomorphSphereTwoTimesCircle P a D hI h0 h1 J hJtarget
  exact F.toHomeomorph.trans sphereTwoTimesCircleModelCopy.equiv.toHomeomorph

@[instance_reducible]
def sphereSelfAttachmentStandardCharts : ChartedSpace E3 (SphereSelfAttachment P a) :=
  DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (sphereSelfAttachmentStandardHomeomorph P a D hI h0 h1 J hJtarget)

theorem sphereSelfAttachmentStandard_isManifold :
    let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
    IsManifold (𝓡 3) ∞ (SphereSelfAttachment P a) :=
  DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
    (I := 𝓡 3) (n := ∞) (sphereSelfAttachmentStandardHomeomorph P a D hI h0 h1 J hJtarget)

def SphereSelfAttachmentStandardDiffeomorph : Type :=
  let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
  Diffeomorph (𝓡 3) (𝓡 3) (SphereSelfAttachment P a) sphereTwoTimesCircleLift.Carrier ∞

def sphereSelfAttachmentStandardDiffeomorph :
    SphereSelfAttachmentStandardDiffeomorph P a D hI h0 h1 J hJtarget :=
  DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := 𝓡 3) (n := ∞) (sphereSelfAttachmentStandardHomeomorph P a D hI h0 h1 J hJtarget)

theorem sphereSelfAttachmentStandardHomeomorph_core
    (x : sphereDoublePuncturedInteriorImage P D hI) :
    sphereSelfAttachmentStandardHomeomorph P a D hI h0 h1 J hJtarget
      (sphereSelfAttachmentCoreMap P a D hI x) =
        sphereSelfAttachmentCoreToSphereProduct P a D hI h0 h1 J hJtarget x := rfl

private theorem identity_change_model_isLocalDiffeomorph
    (f : DoubleCylinder.seamDomain → SphereSelfAttachment P a)
    (x : DoubleCylinder.seamDomain)
    (hf : let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
      IsLocalDiffeomorphAt IC IC ∞ f x) :
    let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorphAt IC (𝓡 3) ∞ f x := by
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  let F : Diffeomorph IC ((𝓡 2).prod (𝓡 1)) (SphereSelfAttachment P a) SphereTwoTimesCircle ∞ :=
    sphereSelfAttachmentDiffeomorphSphereTwoTimesCircle P a D hI h0 h1 J hJtarget
  have h1loc := hf.comp (K := (𝓡 2).prod (𝓡 1)) (P := SphereTwoTimesCircle) (F.isLocalDiffeomorph _)
  have h2loc := h1loc.comp (K := 𝓡 3) (P := sphereTwoTimesCircleLift.Carrier)
    (sphereTwoTimesCircleModelCopy.equiv.isLocalDiffeomorph _)
  let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
  let G : Diffeomorph (𝓡 3) (𝓡 3) (SphereSelfAttachment P a) sphereTwoTimesCircleLift.Carrier ∞ :=
    sphereSelfAttachmentStandardDiffeomorph P a D hI h0 h1 J hJtarget
  have h3 := h2loc.comp (K := 𝓡 3) (P := SphereSelfAttachment P a) (G.symm.isLocalDiffeomorph _)
  have heq : G.symm ∘ (sphereTwoTimesCircleModelCopy.equiv ∘ (F ∘ f)) = f := by
    funext y
    exact (sphereSelfAttachmentStandardHomeomorph P a D hI h0 h1 J hJtarget).symm_apply_apply (f y)
  rwa [heq] at h3

theorem sphereSelfAttachmentStandard_lowerCollar_isLocalDiffeomorphAt
    (hlow : (D : ℝ → ℝ) =ᶠ[𝓝 0] (fun t => t / 15)) (z : S2) :
    let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorphAt IC (𝓡 3) ∞ (sphereSelfAttachmentLowerCollar P a)
      (⟨(z, 0), mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain) :=
  identity_change_model_isLocalDiffeomorph P a D hI h0 h1 J hJtarget _ _
    (sphereSelfAttachmentLowerCollar_isLocalDiffeomorphAt P a D hI h0 h1 J hJtarget hlow z)

theorem sphereSelfAttachmentStandard_upperCollar_isLocalDiffeomorphAt
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1))
    (hupp : (D : ℝ → ℝ) =ᶠ[𝓝 1] (fun t => (16 / (2 - t) - 1) / 15)) (z : S2) :
    let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorphAt IC (𝓡 3) ∞ (sphereSelfAttachmentUpperCollar P a)
      (⟨(z, 0), mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain) :=
  identity_change_model_isLocalDiffeomorph P a D hI h0 h1 J hJtarget _ _
    (sphereSelfAttachmentUpperCollar_isLocalDiffeomorphAt P a D hI h0 h1 J hJtarget hJ hJi hupp z)

theorem sphereSelfAttachmentStandard_core_isLocalDiffeomorph
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1)) :
    let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (sphereSelfAttachmentCoreMap P a D hI) := by
  let _ := sphereSelfAttachmentStandardCharts P a D hI h0 h1 J hJtarget
  let G : Diffeomorph (𝓡 3) (𝓡 3) (SphereSelfAttachment P a) sphereTwoTimesCircleLift.Carrier ∞ :=
    sphereSelfAttachmentStandardDiffeomorph P a D hI h0 h1 J hJtarget
  have h := DifferentialGeometry.isLocalDiffeomorph_comp G.symm.isLocalDiffeomorph
    (sphereSelfAttachmentCoreToSphereProduct_isLocalDiffeomorph P a D hI h0 h1 J hJtarget hJ hJi)
  have heq : G.symm ∘ sphereSelfAttachmentCoreToSphereProduct P a D hI h0 h1 J hJtarget =
      sphereSelfAttachmentCoreMap P a D hI := by
    funext x
    exact (sphereSelfAttachmentStandardHomeomorph P a D hI h0 h1 J hJtarget).symm_apply_apply _
  rwa [heq] at h

end DifferentialGeometry.Topology.Manifold
