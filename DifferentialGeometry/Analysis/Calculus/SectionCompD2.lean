import DifferentialGeometry.Analysis.Calculus.MovingImplicit

set_option autoImplicit false

/-!
# Second derivative of a section composition

This file isolates the Banach-calculus identity behind the full-state
local-addition formula.  For a map `F (p, x)` composed with a section
`p ↦ (p, v p)`, its second derivative splits into the vertical derivative
of `F` applied to `D²v` and a term depending only on the first jet of `v`.
-/

noncomputable section

open Filter
open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis

private theorem fderiv_clm_const
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    {c : P → X →L[Real] Y} {p : P}
    (hc : DifferentiableAt Real c p) (x : X) (a : P) :
    fderiv Real (fun z ↦ c z x) p a = fderiv Real c p a x := by
  rw [fderiv_clm_apply hc (differentiableAt_const x)]
  simp [ContinuousLinearMap.flip_apply]

/-- The second derivative of `p ↦ F (p, v p)` has exactly one term
containing `D²v`: the vertical derivative of `F` applied to `D²v`. -/
theorem sectionCompD2
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    (F : P × X → Y) (v : P → X) (p a b : P)
    (hF : ContDiffAt Real 2 F (p, v p))
    (hv : ContDiffAt Real 2 v p) :
    fderiv Real (fderiv Real (fun z ↦ F (z, v z))) p a b =
      partialFDeriv₂ F p (v p)
          (fderiv Real (fderiv Real v) p a b) +
        fderiv Real (fderiv Real F) (p, v p)
          (a, fderiv Real v p a) (b, fderiv Real v p b) := by
  let G : P → P × X := fun z ↦ (id z, v z)
  let H : P → Y := fun z ↦ F (G z)
  let A : P → (P × X →L[Real] Y) := fun z ↦ fderiv Real F (G z)
  let U : P → P × X := fun z ↦ (b, fderiv Real v z b)
  have hG : ContDiffAt Real 2 G p := by
    simpa only [G] using (contDiffAt_id.prodMk hv)
  have hH : ContDiffAt Real 2 H p := by
    simpa only [H, Function.comp_apply] using hF.comp p hG
  have hGdiff : DifferentiableAt Real G p :=
    hG.differentiableAt (by norm_num)
  have hvDiff : DifferentiableAt Real v p :=
    hv.differentiableAt (by norm_num)
  have hvDeriv : DifferentiableAt Real (fderiv Real v) p :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hFDeriv : DifferentiableAt Real (fderiv Real F) (G p) := by
    simpa only [G] using
      (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hHDeriv : DifferentiableAt Real (fderiv Real H) p :=
    (hH.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA : DifferentiableAt Real A p := by
    simpa only [A, Function.comp_apply] using hFDeriv.comp p hGdiff
  have hvApply : DifferentiableAt Real (fun z ↦ fderiv Real v z b) p :=
    hvDeriv.clm_apply (differentiableAt_const b)
  have hU : DifferentiableAt Real U p := by
    simpa only [U] using (differentiableAt_const b).prodMk hvApply
  have hG_apply (c : P) :
      fderiv Real G p c = (c, fderiv Real v p c) := by
    dsimp only [G]
    rw [DifferentiableAt.fderiv_prodMk differentiableAt_id hvDiff]
    simp only [ContinuousLinearMap.prod_apply, fderiv_id,
      ContinuousLinearMap.id_apply]
  have hU_apply :
      fderiv Real U p a =
        (0, fderiv Real (fderiv Real v) p a b) := by
    dsimp only [U]
    rw [DifferentiableAt.fderiv_prodMk (differentiableAt_const b) hvApply]
    simp only [ContinuousLinearMap.prod_apply]
    rw [fderiv_clm_const hvDeriv b a]
    simp
  have hA_apply :
      fderiv Real A p a =
        fderiv Real (fderiv Real F) (G p)
          (a, fderiv Real v p a) := by
    change fderiv Real (fun z ↦ fderiv Real F (G z)) p a = _
    rw [fderiv_comp' p hFDeriv hGdiff, ContinuousLinearMap.comp_apply,
      hG_apply]
  have hvEventually : ∀ᶠ z in nhds p, ContDiffAt Real 2 v z :=
    hv.eventually (by norm_num)
  have hFEventually : ∀ᶠ z in nhds p, ContDiffAt Real 2 F (G z) :=
    hG.continuousAt (hF.eventually (by norm_num))
  have hfirst :
      (fun z ↦ fderiv Real H z b) =ᶠ[nhds p]
        (fun z ↦ A z (U z)) := by
    filter_upwards [hvEventually, hFEventually] with z hzv hzF
    have hzvDiff : DifferentiableAt Real v z :=
      hzv.differentiableAt (by norm_num)
    have hGzDiff : DifferentiableAt Real G z := by
      simpa only [G] using differentiableAt_id.prodMk hzvDiff
    have hcomp :
        fderiv Real H z =
          (fderiv Real F (G z)).comp (fderiv Real G z) := by
      simpa only [H] using
        fderiv_comp' z (hzF.differentiableAt (by norm_num)) hGzDiff
    have hGz_apply :
        fderiv Real G z b = (b, fderiv Real v z b) := by
      dsimp only [G]
      rw [DifferentiableAt.fderiv_prodMk differentiableAt_id hzvDiff]
      simp only [ContinuousLinearMap.prod_apply, fderiv_id,
        ContinuousLinearMap.id_apply]
    dsimp only [A, U]
    rw [hcomp, ContinuousLinearMap.comp_apply, hGz_apply]
  have hderivEq :
      fderiv Real (fun z ↦ fderiv Real H z b) p a =
        fderiv Real (fun z ↦ A z (U z)) p a :=
    congrArg (fun L : P →L[Real] Y ↦ L a) hfirst.fderiv_eq
  have hleft :
      fderiv Real (fun z ↦ fderiv Real H z b) p a =
        fderiv Real (fderiv Real H) p a b :=
    fderiv_clm_const hHDeriv b a
  have hright :
      fderiv Real (fun z ↦ A z (U z)) p a =
        partialFDeriv₂ F p (v p)
            (fderiv Real (fderiv Real v) p a b) +
          fderiv Real (fderiv Real F) (p, v p)
            (a, fderiv Real v p a) (b, fderiv Real v p b) := by
    rw [fderiv_clm_apply hA hU]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
    rw [hU_apply, hA_apply]
    simp only [A, U, G, id_eq, partialFDeriv₂, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply]
  change fderiv Real (fderiv Real H) p a b = _
  calc
    _ = fderiv Real (fun z ↦ fderiv Real H z b) p a := hleft.symm
    _ = fderiv Real (fun z ↦ A z (U z)) p a := hderivEq
    _ = _ := hright

/-- If the vertical derivative is invertible, subtracting the first-jet
remainder and applying its inverse recovers the top derivative of the
section exactly. -/
theorem sectionD2_cancel
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    (F : P × X → Y) (v : P → X) (p a b : P)
    (hF : ContDiffAt Real 2 F (p, v p))
    (hv : ContDiffAt Real 2 v p)
    (hJ : (partialFDeriv₂ F p (v p)).IsInvertible) :
    (partialFDeriv₂ F p (v p)).inverse
        (fderiv Real (fderiv Real (fun z ↦ F (z, v z))) p a b -
          fderiv Real (fderiv Real F) (p, v p)
            (a, fderiv Real v p a) (b, fderiv Real v p b)) =
      fderiv Real (fderiv Real v) p a b := by
  rw [sectionCompD2 F v p a b hF hv, add_sub_cancel_right]
  exact ContinuousLinearMap.IsInvertible.inverse_apply_self hJ _

end Analysis
end DifferentialGeometry
