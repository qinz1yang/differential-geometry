import DifferentialGeometry.Topology.Manifold.CylinderCollar.NormalExtension

set_option autoImplicit false
noncomputable section

open Set Function Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev EC := E2 × ℝ

theorem axial_derivative_ne_zero_of_zero_section
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (hsource : ∀ p : S2, (p, 0) ∈ A.source)
    (hzero : ∀ p : S2, (A (p, 0)).2 = 0) (p : S2) :
    deriv (fun t => (A (p, t)).2) 0 ≠ 0 := by
  have hA : MDifferentiableAt SphereCylinderModel SphereCylinderModel A (p, 0) :=
    A.mdifferentiableAt (by simp) (hsource p)
  let D : EC →L[ℝ] EC := mfderiv SphereCylinderModel SphereCylinderModel A (p, 0)
  have hhorizontal (v : E2) : (D (v, 0)).2 = 0 := by
    have hh := mfderiv_comp_apply p hA
      ((contMDiff_id.prodMk contMDiff_const : ContMDiff (𝓡 2) SphereCylinderModel ∞ (fun p : S2 => (p, (0 : ℝ)))).mdifferentiableAt (by simp)) v
    have hfst : mfderiv (𝓡 2) SphereCylinderModel (fun p : S2 => (p, (0 : ℝ))) p v = (v, 0) := by
      erw [mfderiv_prodMk mdifferentiableAt_id mdifferentiableAt_const, mfderiv_id, mfderiv_const]
      rfl
    erw [hfst] at hh
    have hsnd := mfderiv_comp_apply p mdifferentiableAt_snd
      (hA.comp p ((contMDiff_id.prodMk contMDiff_const : ContMDiff (𝓡 2) SphereCylinderModel ∞ (fun p : S2 => (p, (0 : ℝ)))).mdifferentiableAt (by simp))) v
    have hfun : (Prod.snd ∘ A ∘ fun p : S2 => (p, (0 : ℝ))) = fun _ => (0 : ℝ) := funext hzero
    change mfderiv (𝓡 2) 𝓘(ℝ) (Prod.snd ∘ A ∘ fun p : S2 => (p, (0 : ℝ))) p v = _ at hsnd
    rw [hfun, mfderiv_const] at hsnd
    erw [mfderiv_snd] at hsnd
    have heq := congrArg Prod.snd hh
    exact heq.symm.trans hsnd.symm
  have hvertical : deriv (fun t => (A (p, t)).2) 0 = (D (0, 1)).2 := by
    have hq : HasMFDerivAt 𝓘(ℝ) SphereCylinderModel (fun t : ℝ => (p, t)) 0
        ((0 : ℝ →L[ℝ] E2).prod (ContinuousLinearMap.id ℝ ℝ)) :=
      (hasMFDerivAt_const p 0).prodMk (hasMFDerivAt_id 0)
    have hh := (hasMFDerivAt_snd (A (p, 0))).comp 0 (hA.hasMFDerivAt.comp 0 hq)
    have heval := hh.mfderiv
    erw [mfderiv_eq_fderiv] at heval
    change (fderiv ℝ (fun t => (A (p, t)).2) 0 : ℝ →L[ℝ] ℝ) = _ at heval
    have hv := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) heval
    exact hv
  intro hneg
  have hz : (D (0, 1)).2 = 0 := hvertical.symm.trans hneg
  have hsurj : Surjective D :=
    (A.isLocalDiffeomorphAt _ _ ∞ (hsource p)).mfderivToContinuousLinearEquiv (by simp) |>.surjective
  obtain ⟨v, hv⟩ := hsurj (0, 1)
  have hsplit : v = (v.1, 0) + v.2 • ((0 : E2), (1 : ℝ)) := by ext <;> simp
  have hbad := congrArg Prod.snd hv
  rw [hsplit, map_add, map_smul] at hbad
  change (D (v.1, 0)).2 + v.2 * (D (0, 1)).2 = 1 at hbad
  rw [hhorizontal, hz, mul_zero, add_zero] at hbad
  norm_num at hbad

end DifferentialGeometry.Topology.Manifold
