import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Construction

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

abbrev BoundaryAttachmentSphere :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def BoundaryAttachmentIsotopic (a a' : BoundaryAttachment) : Prop :=
  ∃ H : ℝ → Diffeomorph (𝓡 2) (𝓡 2)
      BoundaryAttachmentSphere BoundaryAttachmentSphere ∞,
    ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × BoundaryAttachmentSphere => H q.1 q.2) ∧
    ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × BoundaryAttachmentSphere => (H q.1).symm q.2) ∧
    H 0 = a.1 ∧ H 1 = a'.1

def SphereDiffeomorphIsotopicToIdentity
    (f : Diffeomorph (𝓡 2) (𝓡 2)
      BoundaryAttachmentSphere BoundaryAttachmentSphere ∞) : Prop :=
  ∃ J : ℝ → Diffeomorph (𝓡 2) (𝓡 2)
      BoundaryAttachmentSphere BoundaryAttachmentSphere ∞,
    ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × BoundaryAttachmentSphere => J q.1 q.2) ∧
    ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × BoundaryAttachmentSphere => (J q.1).symm q.2) ∧
    J 0 = f ∧ J 1 = Diffeomorph.refl (𝓡 2) BoundaryAttachmentSphere ∞

theorem sphereDiffeomorphIsotopicToIdentity_refl :
    SphereDiffeomorphIsotopicToIdentity
      (Diffeomorph.refl (𝓡 2) BoundaryAttachmentSphere ∞) := by
  refine ⟨fun _ => Diffeomorph.refl (𝓡 2) BoundaryAttachmentSphere ∞,
    contMDiff_snd, contMDiff_snd, rfl, rfl⟩

theorem boundaryAttachmentIsotopic_refl (a : BoundaryAttachment) :
    BoundaryAttachmentIsotopic a a := by
  refine ⟨fun _ => a.1, ?_, ?_, rfl, rfl⟩
  · exact a.1.contMDiff.comp contMDiff_snd
  exact a.1.symm.contMDiff.comp contMDiff_snd

theorem boundaryAttachmentIsotopic_of_sphereDiffeomorphIsotopicToIdentity
    (a a' : BoundaryAttachment)
    (h : SphereDiffeomorphIsotopicToIdentity (a'.1.trans a.1.symm)) :
    BoundaryAttachmentIsotopic a a' := by
  obtain ⟨J, hJ, hJi, hJ0, hJ1⟩ := h
  let H : ℝ → Diffeomorph (𝓡 2) (𝓡 2)
      BoundaryAttachmentSphere BoundaryAttachmentSphere ∞ :=
    fun t => (J (1 - t)).trans a.1
  have htime : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓘(ℝ).prod (𝓡 2)) ∞
      (fun q : ℝ × BoundaryAttachmentSphere => (1 - q.1, q.2)) :=
    (contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd
  have hH : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × BoundaryAttachmentSphere => H q.1 q.2) := by
    dsimp only [H]
    change ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × BoundaryAttachmentSphere => a.1 (J (1 - q.1) q.2))
    exact a.1.contMDiff.comp (hJ.comp htime)
  have hHi : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × BoundaryAttachmentSphere => (H q.1).symm q.2) := by
    dsimp only [H]
    change ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × BoundaryAttachmentSphere => (J (1 - q.1)).symm (a.1.symm q.2))
    exact hJi.comp ((contMDiff_const.sub contMDiff_fst).prodMk
      (a.1.symm.contMDiff.comp contMDiff_snd))
  refine ⟨H, hH, hHi, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro x
    simp only [H, Diffeomorph.coe_trans, Function.comp_apply, sub_zero, hJ1]
    rfl
  · apply Diffeomorph.ext
    intro x
    simp only [H, Diffeomorph.coe_trans, Function.comp_apply, sub_self, hJ0]
    exact Diffeomorph.apply_symm_apply a.1 (a'.1 x)

def SmaleMunkresSphereIsotopy : Prop :=
  ∀ f : Diffeomorph (𝓡 2) (𝓡 2)
      BoundaryAttachmentSphere BoundaryAttachmentSphere ∞,
    f.preservesOrientation (sphereOrientation 2 (by decide))
      (sphereOrientation 2 (by decide)) →
    SphereDiffeomorphIsotopicToIdentity f

theorem boundaryAttachmentIsotopic_of_smaleMunkres
    (h : SmaleMunkresSphereIsotopy) (a a' : BoundaryAttachment) :
    BoundaryAttachmentIsotopic a a' :=
  boundaryAttachmentIsotopic_of_sphereDiffeomorphIsotopicToIdentity a a'
    (h (a'.1.trans a.1.symm)
      (Diffeomorph.preservesOrientation_trans a'.2
        (Diffeomorph.preservesOrientation_symm a.2)))

end DifferentialGeometry.Topology
