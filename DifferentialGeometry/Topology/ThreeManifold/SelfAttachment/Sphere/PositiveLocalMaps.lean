import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.LocalMaps
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.PositiveModel

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

open DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev S3 := Metric.sphere (0 : E4) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

private def angularCollarDiffeomorph (B : E3 ≃ₗᵢ[ℝ] E3) :
    Diffeomorph IC IC SelfAttachment.CollarDomain SelfAttachment.CollarDomain ∞ :=
  (Geometry.sphereDiffeo (n := 2) B).prodCongr
    (Diffeomorph.refl 𝓘(ℝ, ℝ) ConnectedSumQuotient.collarInterval ∞)

private def angularBand (B : E3 ≃ₗᵢ[ℝ] E3) (p : SelfAttachment.bandInterior) :
    SelfAttachment.bandInterior :=
  ⟨(Geometry.sphereDiffeo (n := 2) B p.val.1, p.val.2), mem_univ _, p.property.2⟩

private theorem angularBand_isLocalDiffeomorph (B : E3 ≃ₗᵢ[ℝ] E3) :
    IsLocalDiffeomorph IC IC ∞ (angularBand B) := by
  let F := (Geometry.sphereDiffeo (n := 2) B).prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  have hr := DifferentialGeometry.isLocalDiffeomorph_restrict_open SelfAttachment.bandInterior
    (F.isLocalDiffeomorph.isLocalDiffeomorphOn SelfAttachment.bandInterior)
  intro x
  exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
    (fun p : SelfAttachment.bandInterior => show F p.val ∈ SelfAttachment.bandInterior from
      ⟨mem_univ _, p.property.2⟩) (hr x)

private theorem image_closedBall_common_isometry
    (B : E3 ≃ₗᵢ[ℝ] E3) (c c' : BallChart 3 (𝓡 3) S3)
    (h : ∀ x, c'.chart x = c.chart (B x)) :
    c'.chart '' Metric.closedBall 0 1 = c.chart '' Metric.closedBall 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨B x, by simpa only [Metric.mem_closedBall, dist_zero_right, B.norm_map] using hx, (h x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨B.symm x, by simpa only [Metric.mem_closedBall, dist_zero_right, B.symm.norm_map] using hx, ?_⟩
    rw [h, B.apply_symm_apply]

variable (P : S3)
  (c d : OrientedBallChart standardThreeSphere.toClosedOrientedManifold)
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (B : E3 ≃ₗᵢ[ℝ] E3)
  (hc : ∀ x, c.chart x = (stereographicSmallBallChart P).chart (B x))
  (hd : ∀ x, d.chart x = (oppositeStereographicSmallBallChart P).chart (B x))
  (D : ℝ ≃ₘ[ℝ] ℝ) (hI : D '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1)
  (h0 : D 0 = 0) (h1 : D 1 = 1)

private theorem positiveSphereAttachmentHomeomorph_lower (p : SelfAttachment.CollarDomain) :
    positiveSphereAttachmentHomeomorph P c d hcd B hc hd
      (SelfAttachment.lowerCollar c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph p) =
    SelfAttachment.lowerCollar (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P)
      (stereographicSmallBallChart_disjoint P) antipodalAttachment.toHomeomorph (angularCollarDiffeomorph B p) :=
  SelfAttachment.homeomorphOfAngularTransport_lowerCollar (stereographicSmallBallChart P)
    (oppositeStereographicSmallBallChart P) c.toBallChart d.toBallChart
    (stereographicSmallBallChart_disjoint P) hcd B (fun x _ => hc x) (fun x _ => hd x)
    antipodalAttachment.toHomeomorph _ p

private theorem positiveSphereAttachmentHomeomorph_upper (p : SelfAttachment.CollarDomain) :
    positiveSphereAttachmentHomeomorph P c d hcd B hc hd
      (SelfAttachment.upperCollar c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph p) =
    SelfAttachment.upperCollar (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P)
      (stereographicSmallBallChart_disjoint P) antipodalAttachment.toHomeomorph (angularCollarDiffeomorph B p) :=
  SelfAttachment.homeomorphOfAngularTransport_upperCollar (stereographicSmallBallChart P)
    (oppositeStereographicSmallBallChart P) c.toBallChart d.toBallChart
    (stereographicSmallBallChart_disjoint P) hcd B (fun x _ => hc x) (fun x _ => hd x)
    antipodalAttachment.toHomeomorph _ p

theorem positiveSphereAttachment_lower_localDiffeomorph
    (hlow : (D : ℝ → ℝ) =ᶠ[𝓝 0] (fun t => t / 15)) (z : S2) :
    let _ := sphereSelfAttachmentStandardCharts P antipodalAttachment D hI h0 h1
      sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
    let H := positiveSphereAttachmentHomeomorph P c d hcd B hc hd
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) H
    IsLocalDiffeomorphAt IC (𝓡 3) ∞
      (SelfAttachment.lowerCollar c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph)
      (SelfAttachment.collarZero z) := by
  let _ := sphereSelfAttachmentStandardCharts P antipodalAttachment D hI h0 h1
    sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
  let H := positiveSphereAttachmentHomeomorph P c d hcd B hc hd
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) H
  let G := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := 𝓡 3) (n := ∞) H
  have hraw := sphereSelfAttachmentStandard_lower_localDiffeomorph P antipodalAttachment D hI h0 h1
    sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target hlow
    (Geometry.sphereDiffeo (n := 2) B z)
  have hcomp := ((angularCollarDiffeomorph B).isLocalDiffeomorph (SelfAttachment.collarZero z)).comp
    (K := 𝓡 3) (P := SphereSelfAttachment P antipodalAttachment) hraw
  have hback := hcomp.comp (K := 𝓡 3)
    (P := SelfAttachment.Quotient c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph)
    (G.symm.isLocalDiffeomorph _)
  refine IsLocalDiffeomorphAt.of_eventuallyEq (Eventually.of_forall fun p => ?_) hback
  change SelfAttachment.lowerCollar c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph p =
    H.symm (SelfAttachment.lowerCollar (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P)
      (stereographicSmallBallChart_disjoint P) antipodalAttachment.toHomeomorph (angularCollarDiffeomorph B p))
  rw [← positiveSphereAttachmentHomeomorph_lower P c d hcd B hc hd p, H.symm_apply_apply]

theorem positiveSphereAttachment_upper_localDiffeomorph
    (hupp : (D : ℝ → ℝ) =ᶠ[𝓝 1] (fun t => (16 / (2 - t) - 1) / 15)) (z : S2) :
    let _ := sphereSelfAttachmentStandardCharts P antipodalAttachment D hI h0 h1
      sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
    let H := positiveSphereAttachmentHomeomorph P c d hcd B hc hd
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) H
    IsLocalDiffeomorphAt IC (𝓡 3) ∞
      (SelfAttachment.upperCollar c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph)
      (SelfAttachment.collarZero z) := by
  let _ := sphereSelfAttachmentStandardCharts P antipodalAttachment D hI h0 h1
    sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
  let H := positiveSphereAttachmentHomeomorph P c d hcd B hc hd
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) H
  let G := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := 𝓡 3) (n := ∞) H
  have hraw := sphereSelfAttachmentStandard_upper_localDiffeomorph P antipodalAttachment D hI h0 h1
    sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
    contMDiff_fst contMDiff_fst hupp (Geometry.sphereDiffeo (n := 2) B z)
  have hcomp := ((angularCollarDiffeomorph B).isLocalDiffeomorph (SelfAttachment.collarZero z)).comp
    (K := 𝓡 3) (P := SphereSelfAttachment P antipodalAttachment) hraw
  have hback := hcomp.comp (K := 𝓡 3)
    (P := SelfAttachment.Quotient c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph)
    (G.symm.isLocalDiffeomorph _)
  refine IsLocalDiffeomorphAt.of_eventuallyEq (Eventually.of_forall fun p => ?_) hback
  change SelfAttachment.upperCollar c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph p =
    H.symm (SelfAttachment.upperCollar (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P)
      (stereographicSmallBallChart_disjoint P) antipodalAttachment.toHomeomorph (angularCollarDiffeomorph B p))
  rw [← positiveSphereAttachmentHomeomorph_upper P c d hcd B hc hd p, H.symm_apply_apply]

theorem positiveSphereAttachment_band_localDiffeomorph :
    let _ := sphereSelfAttachmentStandardCharts P antipodalAttachment D hI h0 h1
      sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
    let H := positiveSphereAttachmentHomeomorph P c d hcd B hc hd
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) H
    IsLocalDiffeomorph IC (𝓡 3) ∞
      (SelfAttachment.bandInteriorInclusion c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph) := by
  let _ := sphereSelfAttachmentStandardCharts P antipodalAttachment D hI h0 h1
    sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
  let H := positiveSphereAttachmentHomeomorph P c d hcd B hc hd
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) H
  let G := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := 𝓡 3) (n := ∞) H
  have hraw := sphereSelfAttachmentStandard_bandInterior_isLocalDiffeomorph P antipodalAttachment D hI h0 h1
    sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target contMDiff_fst contMDiff_fst
  have hcomp := DifferentialGeometry.isLocalDiffeomorph_comp hraw (angularBand_isLocalDiffeomorph B)
  have hback := DifferentialGeometry.isLocalDiffeomorph_comp G.symm.isLocalDiffeomorph hcomp
  change IsLocalDiffeomorph IC (𝓡 3) ∞
    (SelfAttachment.bandInteriorInclusion c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph)
  intro x
  refine IsLocalDiffeomorphAt.of_eventuallyEq (Eventually.of_forall fun p => ?_) (hback x)
  change SelfAttachment.bandInteriorInclusion c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph p =
    H.symm (SelfAttachment.bandInteriorInclusion (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P)
      (stereographicSmallBallChart_disjoint P) antipodalAttachment.toHomeomorph (angularBand B p))
  have heq : H (SelfAttachment.bandInteriorInclusion c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph p) =
    SelfAttachment.bandInteriorInclusion (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P)
      (stereographicSmallBallChart_disjoint P) antipodalAttachment.toHomeomorph (angularBand B p) := rfl
  rw [← heq, H.symm_apply_apply]

include hc hd in
private theorem positiveCore_mem_raw (x : SelfAttachment.coreInterior c.toBallChart d.toBallChart) :
    x.val ∈ SelfAttachment.coreInterior (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P) := by
  change x.val ∉ (stereographicSmallBallChart P).chart '' Metric.closedBall 0 1 ∪
    (oppositeStereographicSmallBallChart P).chart '' Metric.closedBall 0 1
  rw [← image_closedBall_common_isometry B (stereographicSmallBallChart P) c.toBallChart hc,
    ← image_closedBall_common_isometry B (oppositeStereographicSmallBallChart P) d.toBallChart hd]
  exact x.property

def positiveSphereAttachmentCoreToRaw (x : SelfAttachment.coreInterior c.toBallChart d.toBallChart) :
    SelfAttachment.coreInterior (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P) :=
  ⟨x.val, positiveCore_mem_raw P c d B hc hd x⟩

private theorem positiveSphereAttachmentCoreToRaw_isLocalDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (positiveSphereAttachmentCoreToRaw P c d B hc hd) := by
  let U : TopologicalSpace.Opens S3 := SelfAttachment.coreInterior c.toBallChart d.toBallChart
  have hmem (x : U) : x.val ∈ SelfAttachment.coreInterior
      (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P) :=
    positiveCore_mem_raw P c d B hc hd x
  intro x
  exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hmem
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val U x)

theorem positiveSphereAttachmentHomeomorph_coreInterior
    (x : SelfAttachment.coreInterior c.toBallChart d.toBallChart) :
    positiveSphereAttachmentHomeomorph P c d hcd B hc hd
      (SelfAttachment.coreInteriorInclusion c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph x) =
    SelfAttachment.coreInteriorInclusion (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P)
      (stereographicSmallBallChart_disjoint P) antipodalAttachment.toHomeomorph
      (positiveSphereAttachmentCoreToRaw P c d B hc hd x) := rfl

theorem positiveSphereAttachment_core_localDiffeomorph :
    let _ := sphereSelfAttachmentStandardCharts P antipodalAttachment D hI h0 h1
      sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
    let H := positiveSphereAttachmentHomeomorph P c d hcd B hc hd
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) H
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (SelfAttachment.coreInteriorInclusion c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph) := by
  let _ := sphereSelfAttachmentStandardCharts P antipodalAttachment D hI h0 h1
    sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
  let H := positiveSphereAttachmentHomeomorph P c d hcd B hc hd
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) H
  let G := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := 𝓡 3) (n := ∞) H
  have hraw := sphereSelfAttachmentStandard_coreInterior_isLocalDiffeomorph P antipodalAttachment D hI h0 h1
    sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target contMDiff_fst contMDiff_fst
  have hf := positiveSphereAttachmentCoreToRaw_isLocalDiffeomorph P c d B hc hd
  have hcomp := DifferentialGeometry.isLocalDiffeomorph_comp hraw hf
  have hback := DifferentialGeometry.isLocalDiffeomorph_comp G.symm.isLocalDiffeomorph hcomp
  change IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
    (SelfAttachment.coreInteriorInclusion c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph)
  intro x
  refine IsLocalDiffeomorphAt.of_eventuallyEq (Eventually.of_forall fun p => ?_) (hback x)
  change SelfAttachment.coreInteriorInclusion c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph p =
    H.symm (SelfAttachment.coreInteriorInclusion (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P)
      (stereographicSmallBallChart_disjoint P) antipodalAttachment.toHomeomorph (positiveSphereAttachmentCoreToRaw P c d B hc hd p))
  rw [← positiveSphereAttachmentHomeomorph_coreInterior P c d hcd B hc hd p, H.symm_apply_apply]

theorem positiveSphereAttachmentHomeomorph_coreImage
    (x : SelfAttachment.coreInterior c.toBallChart d.toBallChart)
    (hx : x.val ∈ sphereDoublePuncturedInteriorImage P D hI) :
    positiveSphereAttachmentHomeomorph P c d hcd B hc hd
      (SelfAttachment.coreInteriorInclusion c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph x) =
      sphereSelfAttachmentCoreMap P antipodalAttachment D hI ⟨x.val, hx⟩ := by
  obtain ⟨hraw, heq⟩ := sphereSelfAttachmentCoreMap_eq P antipodalAttachment D hI ⟨x.val, hx⟩
  rw [heq]
  rfl

end DifferentialGeometry.Topology
