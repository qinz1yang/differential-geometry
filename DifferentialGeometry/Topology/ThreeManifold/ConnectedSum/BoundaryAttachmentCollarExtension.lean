import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.QuotientTransport
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BoundaryAttachmentIsotopy

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff

open Set Function

namespace DifferentialGeometry.Topology

universe u v

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

def boundaryAttachmentDiscrepancy (a a' : BoundaryAttachment) :
    Diffeomorph (𝓡 2) (𝓡 2) BoundaryAttachmentSphere BoundaryAttachmentSphere ∞ :=
  a'.1.trans a.1.symm

theorem boundaryAttachmentDiscrepancy_apply (a a' : BoundaryAttachment)
    (z : BoundaryAttachmentSphere) :
    boundaryAttachmentDiscrepancy a a' z = a.1.symm (a'.1 z) := by
  rw [boundaryAttachmentDiscrepancy, Diffeomorph.coe_trans, Function.comp_apply]

theorem boundaryAttachmentDiscrepancy_preservesOrientation (a a' : BoundaryAttachment) :
    (boundaryAttachmentDiscrepancy a a').preservesOrientation
      (sphereOrientation 2 (by decide)) (sphereOrientation 2 (by decide)) :=
  Diffeomorph.preservesOrientation_trans a'.2 (Diffeomorph.preservesOrientation_symm a.2)

theorem sphereDiffeomorphIsotopicToIdentity_discrepancy_of_boundaryAttachmentIsotopic
    {a a' : BoundaryAttachment} (h : BoundaryAttachmentIsotopic a a') :
    SphereDiffeomorphIsotopicToIdentity (boundaryAttachmentDiscrepancy a a') := by
  obtain ⟨H, hH, hHi, hH0, hH1⟩ := h
  refine ⟨fun t => (H (1 - t)).trans a.1.symm, ?_, ?_, ?_, ?_⟩
  · have htime : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓘(ℝ).prod (𝓡 2)) ∞
        (fun q : ℝ × BoundaryAttachmentSphere => (1 - q.1, q.2)) :=
      (contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd
    have hcomp : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × BoundaryAttachmentSphere => a.1.symm (H (1 - q.1) q.2)) :=
      a.1.symm.contMDiff.comp (hH.comp htime)
    simpa only [Diffeomorph.coe_trans, Function.comp_apply] using hcomp
  · have hsymm : (fun q : ℝ × BoundaryAttachmentSphere =>
        (((H (1 - q.1)).trans a.1.symm).symm) q.2) =
        fun q : ℝ × BoundaryAttachmentSphere => (H (1 - q.1)).symm (a.1 q.2) := by
      funext q
      rw [Diffeomorph.symm_trans', Diffeomorph.coe_trans, Function.comp_apply]
      exact congrArg (fun g : Diffeomorph (𝓡 2) (𝓡 2) BoundaryAttachmentSphere
          BoundaryAttachmentSphere ∞ => (H (1 - q.1)).symm (g q.2))
        (Diffeomorph.ext fun _ => rfl)
    have hcomp : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × BoundaryAttachmentSphere => (H (1 - q.1)).symm (a.1 q.2)) :=
      hHi.comp (((contMDiff_const.sub contMDiff_fst).prodMk
        (a.1.contMDiff.comp contMDiff_snd)))
    rw [hsymm]
    exact hcomp
  · simp only [boundaryAttachmentDiscrepancy, sub_zero, hH1]
  · simp only [sub_self, hH0, Diffeomorph.self_trans_symm]

theorem boundaryAttachmentIsotopic_iff_sphereDiffeomorphIsotopicToIdentity_discrepancy
    (a a' : BoundaryAttachment) :
    BoundaryAttachmentIsotopic a a' ↔
      SphereDiffeomorphIsotopicToIdentity (boundaryAttachmentDiscrepancy a a') :=
  ⟨sphereDiffeomorphIsotopicToIdentity_discrepancy_of_boundaryAttachmentIsotopic,
    boundaryAttachmentIsotopic_of_sphereDiffeomorphIsotopicToIdentity a a'⟩

theorem sphereDiffeomorphIsotopicToIdentity_inv_trans_of_boundaryAttachmentIsotopic
    {a a' : BoundaryAttachment} (h : BoundaryAttachmentIsotopic a a') :
    SphereDiffeomorphIsotopicToIdentity (a.1.symm.trans a'.1) := by
  obtain ⟨H, hH, hHi, hH0, hH1⟩ := h
  refine ⟨fun t => a.1.symm.trans (H (1 - t)), ?_, ?_, ?_, ?_⟩
  · have htime : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓘(ℝ).prod (𝓡 2)) ∞
        (fun q : ℝ × BoundaryAttachmentSphere => (1 - q.1, a.1.symm q.2)) :=
      (contMDiff_const.sub contMDiff_fst).prodMk (a.1.symm.contMDiff.comp contMDiff_snd)
    have hcomp : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × BoundaryAttachmentSphere => H (1 - q.1) (a.1.symm q.2)) :=
      hH.comp htime
    simpa only [Diffeomorph.coe_trans, Function.comp_apply] using hcomp
  · have hsymm : (fun q : ℝ × BoundaryAttachmentSphere =>
        ((a.1.symm.trans (H (1 - q.1))).symm) q.2) =
        fun q : ℝ × BoundaryAttachmentSphere => a.1 ((H (1 - q.1)).symm q.2) := by
      funext q
      rw [Diffeomorph.symm_trans', Diffeomorph.coe_trans, Function.comp_apply]
      exact congrArg (fun g : Diffeomorph (𝓡 2) (𝓡 2) BoundaryAttachmentSphere
          BoundaryAttachmentSphere ∞ => g ((H (1 - q.1)).symm q.2))
        (Diffeomorph.ext fun _ => rfl)
    have hcomp : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × BoundaryAttachmentSphere => a.1 ((H (1 - q.1)).symm q.2)) :=
      a.1.contMDiff.comp (hHi.comp ((contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd))
    rw [hsymm]
    exact hcomp
  · simp only [sub_zero, hH1]
  · simp only [sub_self, hH0, Diffeomorph.symm_trans_self]

private theorem preservesOrientation_self_of_opposite_opposite
    {f : Diffeomorph (𝓡 2) (𝓡 2) BoundaryAttachmentSphere BoundaryAttachmentSphere ∞}
    (h : f.preservesOrientation (sphereOrientation 2 (by decide)).opposite
      (sphereOrientation 2 (by decide)).opposite) :
    f.preservesOrientation (sphereOrientation 2 (by decide))
      (sphereOrientation 2 (by decide)) := by
  intro x
  have hx := h x
  rw [ManifoldOrientation.opposite_orientation, ManifoldOrientation.opposite_orientation,
    Orientation.map_neg] at hx
  exact neg_injective hx

def SphereCollarExtension (N : ConnectedClosedOrientedManifold.{u} 3)
    (d : OrientedBallChart N.toClosedOrientedManifold) : Prop :=
  ∀ f : Diffeomorph (𝓡 2) (𝓡 2) BoundaryAttachmentSphere BoundaryAttachmentSphere ∞,
    f.preservesOrientation (sphereOrientation 2 (by decide)) (sphereOrientation 2 (by decide)) →
    SphereDiffeomorphIsotopicToIdentity f →
    ∃ Ψ : N.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N.Carrier,
      Ψ.preservesOrientation N.orientation N.orientation ∧
      Ψ '' (d.toBallChart.chart '' Metric.ball (0 : E3) 1) =
        d.toBallChart.chart '' Metric.ball (0 : E3) 1 ∧
      ∀ z : BoundaryAttachmentSphere,
        Ψ (d.toBallChart.chart (z : E3)) =
          d.toBallChart.chart ((f z : BoundaryAttachmentSphere) : E3)

def BoundaryAttachmentCollarExtension (N : ConnectedClosedOrientedManifold.{u} 3)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a a' : BoundaryAttachment) : Prop :=
  ∃ Ψ : N.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N.Carrier,
    Ψ.preservesOrientation N.orientation N.orientation ∧
    Ψ '' (d.toBallChart.chart '' Metric.ball (0 : E3) 1) =
      d.toBallChart.chart '' Metric.ball (0 : E3) 1 ∧
    ∀ z : BoundaryAttachmentSphere,
      Ψ (d.toBallChart.chart (a.1 z : E3)) = d.toBallChart.chart (a'.1 z : E3)

theorem boundaryAttachmentCollarExtension_of_sphereCollarExtension
    {N : ConnectedClosedOrientedManifold.{u} 3}
    {d : OrientedBallChart N.toClosedOrientedManifold} {a a' : BoundaryAttachment}
    (h : SphereCollarExtension N d) (hiso : BoundaryAttachmentIsotopic a a') :
    BoundaryAttachmentCollarExtension N d a a' := by
  obtain ⟨Ψ, hΨo, hΨball, hΨbdry⟩ :=
    h (a.1.symm.trans a'.1)
      (preservesOrientation_self_of_opposite_opposite
        (Diffeomorph.preservesOrientation_trans (Diffeomorph.preservesOrientation_symm a.2) a'.2))
      (sphereDiffeomorphIsotopicToIdentity_inv_trans_of_boundaryAttachmentIsotopic hiso)
  refine ⟨Ψ, hΨo, hΨball, fun z => ?_⟩
  rw [hΨbdry (a.1 z), Diffeomorph.coe_trans, Function.comp_apply,
    Diffeomorph.symm_apply_apply]

theorem boundaryAttachmentCollarExtension_refl
    (N : ConnectedClosedOrientedManifold.{u} 3)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    BoundaryAttachmentCollarExtension N d a a :=
  ⟨Diffeomorph.refl (𝓡 3) N.Carrier ∞,
    Diffeomorph.preservesOrientation_refl N.orientation, by simp, fun _ => rfl⟩

theorem nonempty_homeomorph_smoothConnectedSum_of_boundaryAttachmentCollarExtension
    {M : ConnectedClosedOrientedManifold.{u} 3}
    {N : ConnectedClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) {a a' : BoundaryAttachment}
    (h : BoundaryAttachmentCollarExtension N d a a') :
    Nonempty ((smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier ≃ₜ
      (smoothConnectedSum M N c d a').toConnectedClosedOrientedManifold.Carrier) := by
  obtain ⟨Ψ, -, hΨball, hΨbdry⟩ := h
  exact ⟨ConnectedSumQuotient.homeomorphOfBallImage c.toBallChart c.toBallChart
    d.toBallChart d.toBallChart a.1.toHomeomorph a'.1.toHomeomorph
    (Homeomorph.refl _) Ψ.toHomeomorph (by simp) hΨball (Homeomorph.refl _)
    (by intro z; rfl)
    (by
      intro z
      simpa using hΨbdry z)⟩

theorem nonempty_homeomorph_smoothConnectedSum_of_sphereCollarExtension
    {M : ConnectedClosedOrientedManifold.{u} 3}
    {N : ConnectedClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) {a a' : BoundaryAttachment}
    (h : SphereCollarExtension N d) (hiso : BoundaryAttachmentIsotopic a a') :
    Nonempty ((smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier ≃ₜ
      (smoothConnectedSum M N c d a').toConnectedClosedOrientedManifold.Carrier) :=
  nonempty_homeomorph_smoothConnectedSum_of_boundaryAttachmentCollarExtension c d
    (boundaryAttachmentCollarExtension_of_sphereCollarExtension h hiso)

theorem nonempty_homeomorph_smoothConnectedSum_of_smaleMunkres_and_sphereCollarExtension
    {M : ConnectedClosedOrientedManifold.{u} 3}
    {N : ConnectedClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a a' : BoundaryAttachment)
    (hsm : SmaleMunkresSphereIsotopy) (h : SphereCollarExtension N d) :
    Nonempty ((smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier ≃ₜ
      (smoothConnectedSum M N c d a').toConnectedClosedOrientedManifold.Carrier) :=
  nonempty_homeomorph_smoothConnectedSum_of_sphereCollarExtension c d h
    (boundaryAttachmentIsotopic_of_smaleMunkres hsm a a')

def boundaryAttachmentCollarExtensionOrientedDiffeomorphism
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) : Prop :=
  ∀ a a' : BoundaryAttachment, BoundaryAttachmentCollarExtension N d a a' →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum M N c d a').toConnectedClosedOrientedManifold.toClosedOrientedManifold)

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_of_smaleMunkres_and_sphereCollarExtension
    {M : ConnectedClosedOrientedManifold.{u} 3}
    {N : ConnectedClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a a' : BoundaryAttachment)
    (hsm : SmaleMunkresSphereIsotopy) (hsc : SphereCollarExtension N d)
    (hsmooth : boundaryAttachmentCollarExtensionOrientedDiffeomorphism M N c d) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum M N c d a').toConnectedClosedOrientedManifold.toClosedOrientedManifold) :=
  hsmooth a a'
    (boundaryAttachmentCollarExtension_of_sphereCollarExtension hsc
      (boundaryAttachmentIsotopic_of_smaleMunkres hsm a a'))

end DifferentialGeometry.Topology
