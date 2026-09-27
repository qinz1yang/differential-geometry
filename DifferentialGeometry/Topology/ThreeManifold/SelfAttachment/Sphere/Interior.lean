import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.Smooth
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.DoubleCylinderInterior

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

def sphereSelfAttachmentCoreInterior (p : DoubleCylinder.Interior) : SphereSelfAttachment P a :=
  SelfAttachment.coreInclusion (stereographicSmallBallChart P)
    (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P) a.toHomeomorph
    (sphereDoublePuncturedHomeomorph P
      (p.val.1, unitIntervalRestriction D hI ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩))

def sphereSelfAttachmentBandInterior (p : DoubleCylinder.Interior) : SphereSelfAttachment P a :=
  SelfAttachment.bandInclusion (stereographicSmallBallChart P)
    (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P) a.toHomeomorph
    (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)

theorem sphereSelfAttachmentCoreInterior_isLocalDiffeomorph
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1)) :
    let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorph IC IC ∞ (sphereSelfAttachmentCoreInterior P a D hI) := by
  let J' := monodromyIsotopy a J hJtarget
  let _ := sphereMappingTorusChartedSpace J'.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  have hbase := DoubleCylinder.interiorCore_isLocalDiffeomorph J' hJ hJi
  have hH := (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := IC) (n := ∞) (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1).symm).symm.isLocalDiffeomorph
  have hcomp := DifferentialGeometry.isLocalDiffeomorph_comp hH hbase
  have heq : (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1) ∘
      DoubleCylinder.interiorCore (sphereSelfAttachmentMonodromy a) =
        sphereSelfAttachmentCoreInterior P a D hI := by
    funext p
    exact sphereSelfAttachmentReparametrizedHomeomorph_core P a D hI h0 h1
      (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)
  change IsLocalDiffeomorph IC IC ∞ ((sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1) ∘
    DoubleCylinder.interiorCore (sphereSelfAttachmentMonodromy a)) at hcomp
  rwa [heq] at hcomp

theorem sphereSelfAttachmentBandInterior_isLocalDiffeomorph
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1)) :
    let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorph IC IC ∞ (sphereSelfAttachmentBandInterior P a) := by
  let J' := monodromyIsotopy a J hJtarget
  let _ := sphereMappingTorusChartedSpace J'.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (DoubleCylinder.mappingTorusHomeomorph J'.target)
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  have hbase := DoubleCylinder.interiorBand_isLocalDiffeomorph J' hJ hJi
  have hH := (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := IC) (n := ∞) (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1).symm).symm.isLocalDiffeomorph
  have hcomp := DifferentialGeometry.isLocalDiffeomorph_comp hH hbase
  have heq : (sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1) ∘
      DoubleCylinder.interiorBand (sphereSelfAttachmentMonodromy a) =
        sphereSelfAttachmentBandInterior P a := by
    funext p
    exact sphereSelfAttachmentReparametrizedHomeomorph_band P a D hI h0 h1
      (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)
  change IsLocalDiffeomorph IC IC ∞ ((sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1) ∘
    DoubleCylinder.interiorBand (sphereSelfAttachmentMonodromy a)) at hcomp
  rwa [heq] at hcomp

private def cylinderReparametrization : Diffeomorph IC IC (S2 × ℝ) (S2 × ℝ) ∞ where
  toFun p := (-p.1, D p.2)
  invFun p := (-p.1, D.symm p.2)
  left_inv p := Prod.ext (neg_neg p.1) (D.symm_apply_apply p.2)
  right_inv p := Prod.ext (neg_neg p.1) (D.apply_symm_apply p.2)
  contMDiff_toFun :=
    ((sphereAntipodalDiffeomorph (E := E3) (n := 2)).contMDiff.comp contMDiff_fst).prodMk
      (D.contMDiff.comp contMDiff_snd)
  contMDiff_invFun :=
    ((sphereAntipodalDiffeomorph (E := E3) (n := 2)).contMDiff.comp contMDiff_fst).prodMk
      (D.symm.contMDiff.comp contMDiff_snd)

def sphereDoublePuncturedInterior (p : DoubleCylinder.Interior) : S3 :=
  (sphereDoublePuncturedHomeomorph P
    (p.val.1, unitIntervalRestriction D hI ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)).val

theorem sphereDoublePuncturedInterior_isLocalDiffeomorph :
    IsLocalDiffeomorph IC (𝓡 3) ∞ (sphereDoublePuncturedInterior P D hI) := by
  have hres := DifferentialGeometry.isLocalDiffeomorph_restrict_open DoubleCylinder.Interior
    ((cylinderReparametrization D).isLocalDiffeomorph.isLocalDiffeomorphOn DoubleCylinder.Interior)
  intro p
  have hmem : D p.val.2 ∈ Icc (0 : ℝ) 1 := by
    rw [← hI]
    exact ⟨p.val.2, ⟨p.property.2.1.le, p.property.2.2.le⟩, rfl⟩
  have hrad := stereographic_radial_isLocalDiffeomorphAt P (1 / 2) 8 (by norm_num)
    ((cylinderReparametrization D) p.val) (by change 0 < 1 / 2 + (8 - 1 / 2) * D p.val.2; nlinarith [hmem.1])
  have hcomp := (hres p).comp (K := 𝓡 3) (P := S3) hrad
  exact hcomp

theorem sphereDoublePuncturedInterior_injective : Injective (sphereDoublePuncturedInterior P D hI) := by
  intro p q h
  have hq := (sphereDoublePuncturedHomeomorph P).injective (Subtype.ext h)
  apply Subtype.ext
  refine Prod.ext (congrArg (fun x : S2 × Icc (0 : ℝ) 1 => x.1) hq) ?_
  have ht := congrArg (fun x : S2 × Icc (0 : ℝ) 1 => x.2.val) hq
  exact D.injective ht

def sphereDoublePuncturedInteriorImage : TopologicalSpace.Opens S3 :=
  ⟨range (sphereDoublePuncturedInterior P D hI),
    (sphereDoublePuncturedInterior_isLocalDiffeomorph P D hI).isOpenMap.isOpen_range⟩

def sphereDoublePuncturedInteriorDiffeomorph :
    Diffeomorph IC (𝓡 3) DoubleCylinder.Interior (sphereDoublePuncturedInteriorImage P D hI) ∞ := by
  have hloc : IsLocalDiffeomorph IC (𝓡 3) ∞
      (fun p : DoubleCylinder.Interior =>
        (⟨sphereDoublePuncturedInterior P D hI p, ⟨p, rfl⟩⟩ : sphereDoublePuncturedInteriorImage P D hI)) := by
    intro p
    exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
      (fun q : DoubleCylinder.Interior => show sphereDoublePuncturedInterior P D hI q ∈
        sphereDoublePuncturedInteriorImage P D hI from ⟨q, rfl⟩)
      (sphereDoublePuncturedInterior_isLocalDiffeomorph P D hI p)
  exact hloc.diffeomorphOfBijective ⟨fun p q hpq =>
    sphereDoublePuncturedInterior_injective P D hI (congrArg (fun x : sphereDoublePuncturedInteriorImage P D hI => x.val) hpq), by
      rintro ⟨q, p, hp⟩
      exact ⟨p, Subtype.ext hp⟩⟩

theorem sphereDoublePuncturedInteriorDiffeomorph_apply (p : DoubleCylinder.Interior) :
    (sphereDoublePuncturedInteriorDiffeomorph P D hI p).val = sphereDoublePuncturedInterior P D hI p := rfl

def sphereSelfAttachmentCoreMap (p : sphereDoublePuncturedInteriorImage P D hI) : SphereSelfAttachment P a :=
  sphereSelfAttachmentCoreInterior P a D hI ((sphereDoublePuncturedInteriorDiffeomorph P D hI).symm p)

theorem sphereSelfAttachmentCoreMap_isLocalDiffeomorph
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1)) :
    let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
    IsLocalDiffeomorph (𝓡 3) IC ∞ (sphereSelfAttachmentCoreMap P a D hI) := by
  let _ := sphereSelfAttachmentChartedSpace P a D hI h0 h1 J hJtarget
  exact DifferentialGeometry.isLocalDiffeomorph_comp
    (sphereSelfAttachmentCoreInterior_isLocalDiffeomorph P a D hI h0 h1 J hJtarget hJ hJi)
    (sphereDoublePuncturedInteriorDiffeomorph P D hI).symm.isLocalDiffeomorph

theorem sphereSelfAttachmentCoreMap_eq (p : sphereDoublePuncturedInteriorImage P D hI) :
    ∃ hp, sphereSelfAttachmentCoreMap P a D hI p =
      SelfAttachment.coreInclusion (stereographicSmallBallChart P)
        (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P)
        a.toHomeomorph ⟨p.val, hp⟩ := by
  let x := (sphereDoublePuncturedInteriorDiffeomorph P D hI).symm p
  let q := sphereDoublePuncturedHomeomorph P
    (x.val.1, unitIntervalRestriction D hI ⟨x.val.2, x.property.2.1.le, x.property.2.2.le⟩)
  have hval : q.val = p.val := by
    have h := congrArg Subtype.val
      ((sphereDoublePuncturedInteriorDiffeomorph P D hI).apply_symm_apply p)
    rw [sphereDoublePuncturedInteriorDiffeomorph_apply] at h
    exact h
  refine ⟨hval ▸ q.property, ?_⟩
  exact congrArg (SelfAttachment.coreInclusion _ _ _ _) (Subtype.ext hval)

end DifferentialGeometry.Topology.Manifold
