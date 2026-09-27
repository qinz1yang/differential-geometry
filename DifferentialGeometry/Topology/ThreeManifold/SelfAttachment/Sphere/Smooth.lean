import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.Collar

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

private abbrev monodromyIsotopy : SphereMappingTorusIsotopy where
  target := sphereSelfAttachmentMonodromy a
  isotopy := J.isotopy
  continuous_apply := J.continuous_apply
  isotopy_zero := J.isotopy_zero
  isotopy_one := J.isotopy_one.trans hJtarget

@[instance_reducible]
def sphereSelfAttachmentChartedSpace :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (SphereSelfAttachment P a) := by
  let J' := monodromyIsotopy a J hJtarget
  let _ := sphereMappingTorusChartedSpace J'.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ)
    (DoubleCylinder.mappingTorusHomeomorph (sphereSelfAttachmentMonodromy a))
  exact DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ)
    (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1).symm

theorem sphereSelfAttachmentLowerCollar_isLocalDiffeomorphAt
    (hlow : (D : ℝ → ℝ) =ᶠ[𝓝 0] (fun t => t / 15)) (z : S2) :
    let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorphAt IC IC ∞ (sphereSelfAttachmentLowerCollar P a)
      (⟨(z, 0), mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain) := by
  let J' := monodromyIsotopy a J hJtarget
  let _ := sphereMappingTorusChartedSpace J'.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  have hbase := DoubleCylinder.lowerSeam_isLocalDiffeomorph J'
  have hH := (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := IC) (n := ∞) (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1).symm).symm.isLocalDiffeomorph
  have hcomp := DifferentialGeometry.isLocalDiffeomorph_comp hH hbase
  have heq := sphereSelfAttachmentReparametrizedHomeomorph_lowerSeam_eventually P a D hI h0 h1 hlow z
  exact IsLocalDiffeomorphAt.of_eventuallyEq heq.symm
    (hcomp (⟨(z, 0), mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain))

theorem sphereSelfAttachmentUpperCollar_isLocalDiffeomorphAt
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1))
    (hupp : (D : ℝ → ℝ) =ᶠ[𝓝 1] (fun t => (16 / (2 - t) - 1) / 15)) (z : S2) :
    let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorphAt IC IC ∞ (sphereSelfAttachmentUpperCollar P a)
      (⟨(z, 0), mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain) := by
  let J' := monodromyIsotopy a J hJtarget
  let _ := sphereMappingTorusChartedSpace J'.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  have hbase := DoubleCylinder.upperSeam_isLocalDiffeomorph J' hJ hJi
  have hH := (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := IC) (n := ∞) (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1).symm).symm.isLocalDiffeomorph
  have hcomp := DifferentialGeometry.isLocalDiffeomorph_comp hH hbase
  have heq := sphereSelfAttachmentReparametrizedHomeomorph_upperSeam_eventually P a D hI h0 h1 hupp z
  exact IsLocalDiffeomorphAt.of_eventuallyEq heq.symm
    (hcomp (⟨(z, 0), mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain))


theorem sphereSelfAttachment_isManifold :
    let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
    IsManifold IC ∞ (SphereSelfAttachment P a) := by
  let J' := monodromyIsotopy a J hJtarget
  let _ := sphereMappingTorusChartedSpace J'.flatten
  let _ : IsManifold IC ∞ (SphereMappingTorus J'.target) :=
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
      (I := IC) (n := ∞) (sphereMappingTorusHomeomorph J'.flatten)
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  let _ : IsManifold IC ∞ (DoubleCylinder.Space J'.target) :=
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
      (I := IC) (n := ∞) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  exact DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
    (I := IC) (n := ∞) (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1).symm

def SphereSelfAttachmentDiffeomorph : Type :=
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  Diffeomorph IC ((𝓡 2).prod (𝓡 1)) (SphereSelfAttachment P a) SphereTwoTimesCircle ∞

def sphereSelfAttachmentDiffeomorphSphereTwoTimesCircle :
    SphereSelfAttachmentDiffeomorph P a D hI h0 h1 J hJtarget := by
  let J' := monodromyIsotopy a J hJtarget
  let _ := sphereMappingTorusChartedSpace J'.flatten
  let _ : IsManifold IC ∞ (SphereMappingTorus J'.target) :=
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
      (I := IC) (n := ∞) (sphereMappingTorusHomeomorph J'.flatten)
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  let _ : IsManifold IC ∞ (DoubleCylinder.Space J'.target) :=
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
      (I := IC) (n := ∞) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  let F := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := IC) (n := ∞) (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1).symm
  let G := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := IC) (n := ∞) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  exact (F.trans G).trans (sphereMappingTorusDiffeomorphSphereTwoTimesCircle J'.flatten)

end DifferentialGeometry.Topology.Manifold
