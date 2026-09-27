import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis.Calculus

universe u v w

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem derivWithin_prod_fst_of_hasFDerivWithinAt
    (F : ℝ × X → Y) (F' : (ℝ × X) →L[ℝ] Y) {J : Set ℝ} {U : Set X}
    {t : ℝ} {y₀ : X} (hy₀ : y₀ ∈ U) (huniq : UniqueDiffWithinAt ℝ J t)
    (hF : HasFDerivWithinAt F F' (J ×ˢ U) (t, y₀)) :
    derivWithin (fun r : ℝ => F (r, y₀)) J t = F' (1, 0) := by
  have hι : HasFDerivWithinAt (fun r : ℝ => (r, y₀))
      (ContinuousLinearMap.inl ℝ ℝ X) J t :=
    (hasFDerivAt_prodMk_left t y₀).hasFDerivWithinAt
  have hmap : MapsTo (fun r : ℝ => (r, y₀)) J (J ×ˢ U) := fun r hr => ⟨hr, hy₀⟩
  have hcomp := hF.comp t hι hmap
  exact (hcomp.hasDerivWithinAt.congr (fun r _ => rfl) rfl).derivWithin huniq

theorem fderiv_prod_snd_of_hasFDerivWithinAt
    (F : ℝ × X → Y) (F' : (ℝ × X) →L[ℝ] Y) {J : Set ℝ} {U : Set X}
    {t : ℝ} {y₀ : X} (ht : t ∈ J) (hU : U ∈ 𝓝 y₀)
    (hF : HasFDerivWithinAt F F' (J ×ˢ U) (t, y₀)) (y' : X) :
    fderiv ℝ (fun y : X => F (t, y)) y₀ y' = F' (0, y') := by
  have hι : HasFDerivAt (fun y : X => (t, y)) (ContinuousLinearMap.inr ℝ ℝ X) y₀ :=
    hasFDerivAt_prodMk_right t y₀
  have hmem : ∀ᶠ y : X in 𝓝 y₀, (t, y) ∈ J ×ˢ U := by
    filter_upwards [hU] with y hy
    exact ⟨ht, hy⟩
  have hcomp := hF.comp_hasFDerivAt y₀ hι hmem
  have h1 : fderiv ℝ (fun y : X => F (t, y)) y₀
      = F'.comp (ContinuousLinearMap.inr ℝ ℝ X) := hcomp.fderiv
  rw [h1]
  rfl

theorem hasDerivWithinAt_prod_curve
    (F : ℝ × X → Y) (F' : (ℝ × X) →L[ℝ] Y) (y : ℝ → X) (y' : X) {J : Set ℝ} {U : Set X}
    {t : ℝ} {y₀ : X} (hy : y t = y₀) (hF : HasFDerivWithinAt F F' (J ×ˢ U) (t, y₀))
    (hy' : HasDerivWithinAt y y' J t) (hmap : ∀ r ∈ J, y r ∈ U) :
    HasDerivWithinAt (fun r : ℝ => F (r, y r)) (F' (1, 0) + F' (0, y')) J t := by
  have hF' : HasFDerivWithinAt F F' (J ×ˢ U) (t, y t) := by rw [hy]; exact hF
  have hid : HasFDerivWithinAt (fun r : ℝ => r) (1 : ℝ →L[ℝ] ℝ) J t :=
    (hasFDerivAt_id t).hasFDerivWithinAt
  have hpair : HasFDerivWithinAt (fun r : ℝ => (r, y r))
      ((1 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.toSpanSingleton ℝ y')) J t :=
    hid.prodMk hy'.hasFDerivWithinAt
  have hmap' : MapsTo (fun r : ℝ => (r, y r)) J (J ×ˢ U) := fun r hr => ⟨hr, hmap r hr⟩
  have hcomp := hF'.comp t hpair hmap'
  have hval : ((F' : (ℝ × X) →L[ℝ] Y) ∘SL
      ((1 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.toSpanSingleton ℝ y'))) (1 : ℝ)
      = F' (1, 0) + F' (0, y') := by
    change F' (((1 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.toSpanSingleton ℝ y')) 1) = _
    have h : ((1 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.toSpanSingleton ℝ y')) 1
        = ((1 : ℝ), y') := by
      simp [ContinuousLinearMap.prod_apply]
    rw [h]
    rw [show ((1 : ℝ), y') = (1, 0) + ((0 : ℝ), y') by simp, map_add]
  have h := hcomp.hasDerivWithinAt.congr (fun r _ => rfl) rfl
  rw [hval] at h
  exact h

end DifferentialGeometry.Analysis.Calculus
