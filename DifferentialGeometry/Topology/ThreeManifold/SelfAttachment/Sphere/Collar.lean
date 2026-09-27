import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.Topology
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.RadialReparametrization
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Collar
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

namespace DoubleCylinder

variable (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo)
  (D : ℝ ≃ₘ[ℝ] ℝ) (hI : D '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1)
  (h0 : D 0 = 0) (h1 : D 1 = 1)

def reparametrizationHomeomorph : Space f ≃ₜ Space f := by
  apply adjunctionSpaceHomeomorphOfHomeomorph
    SelfAttachment.boundaryInclusion (attachingMap f)
    SelfAttachment.boundaryInclusion (attachingMap f)
    (Homeomorph.refl _) (Homeomorph.refl _)
    ((Homeomorph.refl SphereTwo).prodCongr (Manifold.unitIntervalRestriction D hI).toHomeomorph)
  · intro q
    rfl
  · rintro ⟨b, z⟩
    cases b
    · refine Prod.ext (by rfl) (Subtype.ext ?_)
      exact h0
    · refine Prod.ext (by rfl) (Subtype.ext ?_)
      exact h1

theorem reparametrizationHomeomorph_core (p : Cylinder) :
    reparametrizationHomeomorph f D hI h0 h1 (core f p) =
      core f (p.1, Manifold.unitIntervalRestriction D hI p.2) := rfl

theorem reparametrizationHomeomorph_band (p : Cylinder) :
    reparametrizationHomeomorph f D hI h0 h1 (band f p) = band f p := rfl

end DoubleCylinder

namespace Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

variable (P : S3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
  (D : ℝ ≃ₘ[ℝ] ℝ) (hI : D '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1)
  (h0 : D 0 = 0) (h1 : D 1 = 1)

def sphereSelfAttachmentReparametrizedHomeomorph :
    DoubleCylinder.Space (sphereSelfAttachmentMonodromy a) ≃ₜ SphereSelfAttachment P a :=
  (DoubleCylinder.reparametrizationHomeomorph (sphereSelfAttachmentMonodromy a) D hI h0 h1).trans
    (doubleCylinderSphereSelfAttachmentHomeomorph P a)

theorem sphereSelfAttachmentReparametrizedHomeomorph_core (p : DoubleCylinder.Cylinder) :
    sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1
      (DoubleCylinder.core (sphereSelfAttachmentMonodromy a) p) =
      SelfAttachment.coreInclusion (stereographicSmallBallChart P)
        (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P) a.toHomeomorph
        (sphereDoublePuncturedHomeomorph P (p.1, unitIntervalRestriction D hI p.2)) := by
  rw [sphereSelfAttachmentReparametrizedHomeomorph, Homeomorph.trans_apply,
    DoubleCylinder.reparametrizationHomeomorph_core, doubleCylinderSphereSelfAttachmentHomeomorph_core]

theorem sphereSelfAttachmentReparametrizedHomeomorph_band (p : DoubleCylinder.Cylinder) :
    sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1
      (DoubleCylinder.band (sphereSelfAttachmentMonodromy a) p) =
      SelfAttachment.bandInclusion (stereographicSmallBallChart P)
        (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P) a.toHomeomorph p := by
  rw [sphereSelfAttachmentReparametrizedHomeomorph, Homeomorph.trans_apply,
    DoubleCylinder.reparametrizationHomeomorph_band, doubleCylinderSphereSelfAttachmentHomeomorph_band]

private def reversedCollarParameter (p : DoubleCylinder.seamDomain) : SelfAttachment.CollarDomain :=
  (p.val.1, ⟨-p.val.2, by constructor <;> linarith [p.property.2.1, p.property.2.2]⟩)

def sphereSelfAttachmentLowerCollar (p : DoubleCylinder.seamDomain) : SphereSelfAttachment P a :=
  SelfAttachment.lowerCollar (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P)
    (stereographicSmallBallChart_disjoint P) a.toHomeomorph (reversedCollarParameter p)

theorem sphereSelfAttachmentReparametrizedHomeomorph_lowerSeam
    (p : DoubleCylinder.seamDomain) (hgerm : D p.val.2 = p.val.2 / 15) :
    sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1
      (DoubleCylinder.lowerSeam (sphereSelfAttachmentMonodromy a) p) =
      sphereSelfAttachmentLowerCollar P a p := by
  unfold DoubleCylinder.lowerSeam
  split_ifs with ht
  · rw [sphereSelfAttachmentReparametrizedHomeomorph_core]
    rw [sphereSelfAttachmentLowerCollar, SelfAttachment.lowerCollar_of_nonpos _ _ _ _ _
      (by change -p.val.2 ≤ 0; linarith)]
    apply congrArg (SelfAttachment.coreInclusion _ _ _ _)
    apply Subtype.ext
    change (stereographic' 3 P).symm
      (((1 / 2 : ℝ) + (8 - 1 / 2) * D p.val.2) • -p.val.1.val) =
      (stereographicSmallBallChart P).chart ((1 - -p.val.2) • p.val.1.val)
    rw [stereographicSmallBallChart_apply, hgerm]
    congr 1
    module
  · rw [sphereSelfAttachmentReparametrizedHomeomorph_band]
    rw [sphereSelfAttachmentLowerCollar, SelfAttachment.lowerCollar_of_pos _ _ _ _ _
      (by change 0 < -p.val.2; linarith)]
    rfl

theorem sphereSelfAttachmentReparametrizedHomeomorph_lowerSeam_eventually
    (hgerm : (D : ℝ → ℝ) =ᶠ[𝓝 0] (fun t => t / 15)) (z : S2) :
    (fun p : DoubleCylinder.seamDomain =>
      sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1
        (DoubleCylinder.lowerSeam (sphereSelfAttachmentMonodromy a) p)) =ᶠ[
          𝓝 (⟨(z, 0), mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain)]
      sphereSelfAttachmentLowerCollar P a := by
  have ht : Continuous (fun p : DoubleCylinder.seamDomain => p.val.2) :=
    continuous_snd.comp continuous_subtype_val
  filter_upwards [hgerm.comp_tendsto (ht.tendsto
    (⟨(z, 0), mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain))] with p hp
  exact sphereSelfAttachmentReparametrizedHomeomorph_lowerSeam P a D hI h0 h1 p hp


theorem oppositeStereographicSmallBallChart_radial (z : S2) {r : ℝ} (hr : 0 < r) :
    (oppositeStereographicSmallBallChart P).chart (r • (-z).val) =
      (stereographic' 3 P).symm ((-8 / r) • z.val) := by
  rw [oppositeStereographicSmallBallChart_apply, stereographicSmallBallChart_apply]
  have hv : (-(1 / 2 : ℝ)) • (r • (-z).val) = (r / 2) • z.val := by
    change (-(1 / 2 : ℝ)) • (r • -z.val) = _
    module
  rw [hv]
  have hn : ‖(r / 2) • z.val‖ = r / 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), norm_eq_of_mem_sphere, mul_one]
  rw [← stereographicInverse_antipodal (n := 3) P ((r / 2) • z.val)
    (by intro h; rw [h, norm_zero] at hn; linarith), hn, smul_smul]
  congr 2
  field_simp
  ring

private def reversedUpperCollarParameter (p : DoubleCylinder.seamDomain) : SelfAttachment.CollarDomain :=
  ((sphereSelfAttachmentMonodromy a) p.val.1,
    ⟨-p.val.2, by constructor <;> linarith [p.property.2.1, p.property.2.2]⟩)

def sphereSelfAttachmentUpperCollar (p : DoubleCylinder.seamDomain) : SphereSelfAttachment P a :=
  SelfAttachment.upperCollar (stereographicSmallBallChart P) (oppositeStereographicSmallBallChart P)
    (stereographicSmallBallChart_disjoint P) a.toHomeomorph (reversedUpperCollarParameter a p)

theorem sphereSelfAttachmentReparametrizedHomeomorph_upperSeam
    (p : DoubleCylinder.seamDomain)
    (hgerm : D (1 + p.val.2) = (16 / (2 - (1 + p.val.2)) - 1) / 15) :
    sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1
      (DoubleCylinder.upperSeam (sphereSelfAttachmentMonodromy a) p) =
      sphereSelfAttachmentUpperCollar P a p := by
  unfold DoubleCylinder.upperSeam
  split_ifs with ht
  · rw [sphereSelfAttachmentReparametrizedHomeomorph_band]
    by_cases hz : p.val.2 = 0
    · have hseam := SelfAttachment.seam_eq (stereographicSmallBallChart P)
        (oppositeStereographicSmallBallChart P) (stereographicSmallBallChart_disjoint P) a.toHomeomorph
        (true, sphereSelfAttachmentMonodromy a p.val.1)
      rw [sphereSelfAttachmentUpperCollar, SelfAttachment.upperCollar_of_nonneg _ _ _ _ _
        (by change 0 ≤ -p.val.2; rw [hz]; norm_num)]
      convert hseam using 1
      · congr 1
        exact Prod.ext rfl (Subtype.ext (by change 1 - p.val.2 = 1; rw [hz]; ring))
      · congr 1
        apply Subtype.ext
        change (oppositeStereographicSmallBallChart P).chart
          ((1 + -p.val.2) • (a ((sphereSelfAttachmentMonodromy a) p.val.1)).val) = _
        rw [hz]
        norm_num [SelfAttachment.attachingMap]
    · rw [sphereSelfAttachmentUpperCollar, SelfAttachment.upperCollar_of_neg _ _ _ _ _
        (by change -p.val.2 < 0; have := lt_of_le_of_ne ht (Ne.symm hz); linarith)]
      congr 1
  · rw [sphereSelfAttachmentReparametrizedHomeomorph_core]
    rw [sphereSelfAttachmentUpperCollar, SelfAttachment.upperCollar_of_nonneg _ _ _ _ _
      (by change 0 ≤ -p.val.2; linarith)]
    apply congrArg (SelfAttachment.coreInclusion _ _ _ _)
    apply Subtype.ext
    change (stereographic' 3 P).symm
      (((1 / 2 : ℝ) + (8 - 1 / 2) * D (1 + p.val.2)) • -p.val.1.val) =
      (oppositeStereographicSmallBallChart P).chart
        ((1 + -p.val.2) • (a ((sphereSelfAttachmentMonodromy a) p.val.1)).val)
    have haf : a (sphereSelfAttachmentMonodromy a p.val.1) = -p.val.1 :=
      a.apply_symm_apply _
    rw [haf, oppositeStereographicSmallBallChart_radial P _ (by linarith), hgerm]
    congr 1
    have hs : 2 - (1 + p.val.2) = 1 + -p.val.2 := by ring
    rw [hs]
    module

theorem sphereSelfAttachmentReparametrizedHomeomorph_upperSeam_eventually
    (hgerm : (D : ℝ → ℝ) =ᶠ[𝓝 1] (fun t => (16 / (2 - t) - 1) / 15)) (z : S2) :
    (fun p : DoubleCylinder.seamDomain =>
      sphereSelfAttachmentReparametrizedHomeomorph P a D hI h0 h1
        (DoubleCylinder.upperSeam (sphereSelfAttachmentMonodromy a) p)) =ᶠ[
          𝓝 (⟨(z, 0), mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain)]
      sphereSelfAttachmentUpperCollar P a := by
  have ht : Continuous (fun p : DoubleCylinder.seamDomain => 1 + p.val.2) :=
    continuous_const.add (continuous_snd.comp continuous_subtype_val)
  have htend : Tendsto (fun p : DoubleCylinder.seamDomain => 1 + p.val.2)
      (𝓝 (⟨(z, 0), mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain)) (𝓝 1) := by
    simpa only [zero_add, add_zero] using ht.tendsto
      (⟨(z, 0), mem_univ _, by norm_num⟩ : DoubleCylinder.seamDomain)
  filter_upwards [hgerm.comp_tendsto htend] with p hp
  exact sphereSelfAttachmentReparametrizedHomeomorph_upperSeam P a D hI h0 h1 p hp

end Manifold
end DifferentialGeometry.Topology
