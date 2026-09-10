import DifferentialGeometry.Topology.Manifold.RegularLevel.Collar.TransverseFlow
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar
import DifferentialGeometry.Topology.Morse.RegularLevel.Sublevel

set_option autoImplicit false

open Set Manifold
open scoped Topology ContDiff
open DifferentialGeometry.Topology.Morse Poincare.Topology

noncomputable section

namespace Poincare.Manifold.RegularLevel

theorem exists_smoothTwoSidedCollar_of_compact_regularLevel
    {m : ℕ} {f : MorseModel (m + 1) → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ)
    (hK : IsCompact {x | f x = a})
    (hr : ∀ x, f x = a → ¬ IsCriticalPointAt 𝓘(ℝ, MorseModel (m + 1)) f x) :
    let _ := manifoldLevelSetChartedSpace 𝓘(ℝ, MorseModel (m + 1)) f a hf.contMDiff hr
    ∃ c : SmoothTwoSidedCollar 𝓘(ℝ, MorseModel m) 𝓘(ℝ, MorseModel (m + 1))
      (Subtype.val : LevelSetSpace f a → MorseModel (m + 1)),
      ∀ p, f (c.toFun p) = a - p.2 := by
  let _ := manifoldLevelSetChartedSpace 𝓘(ℝ, MorseModel (m + 1)) f a hf.contMDiff hr
  have hr' : ∀ x, f x = a → fderiv ℝ f x ≠ 0 := by
    intro x hx hz
    apply hr x hx
    unfold IsCriticalPointAt
    ext w
    rw [mfderiv_eq_fderiv, hz]
    rfl
  obtain ⟨r, hrpos, U, F, hF, e, hforward, hback, htime, hvalue, hzero⟩ :=
    exists_flowCollar_of_compact_regularLevel hf a hK hr'
  let e' : (LevelSetSpace f a × symmetricOpenInterval r) ≃ₜ U := e
  have hinc : ContMDiff 𝓘(ℝ, MorseModel m) 𝓘(ℝ, MorseModel (m + 1)) ∞
      (Subtype.val : LevelSetSpace f a → MorseModel (m + 1)) :=
    contMDiff_levelSetInclusion 𝓘(ℝ, MorseModel (m + 1)) f a hf.contMDiff hr
  have he : ContMDiff (𝓘(ℝ, MorseModel m).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, MorseModel (m + 1)) ∞
      (e' : LevelSetSpace f a × symmetricOpenInterval r → U) := by
    apply (ContMDiff.subtypeVal_comp_iff U e').mp
    have hp : ContMDiff (𝓘(ℝ, MorseModel m).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, MorseModel (m + 1) × ℝ) ∞
        (fun p : LevelSetSpace f a × symmetricOpenInterval r =>
          ((p.1 : MorseModel (m + 1)), (p.2 : ℝ))) :=
      (hinc.comp contMDiff_fst).prodMk_space
        (contMDiff_subtype_val.comp contMDiff_snd)
    exact (hF.contMDiff.comp hp).congr (fun p => hforward p)
  have hproj : ContMDiff 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, MorseModel (m + 1)) ∞
      (fun y : U => F (y, f y - a)) := by
    exact hF.contMDiff.comp
      (contMDiff_subtype_val.prodMk_space
        ((hf.contMDiff.comp contMDiff_subtype_val).sub contMDiff_const))
  have hprojlevel : ∀ y : U, f (F (y, f y - a)) = a := by
    intro y
    rw [← hback y]
    exact (e'.symm y).1.2
  have hinv₁ : ContMDiff 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, MorseModel m) ∞
      (fun y : U => (e'.symm y).1) := by
    have h := contMDiff_levelSet_factor 𝓘(ℝ, MorseModel (m + 1)) f a hf.contMDiff hr
      (fun y : U => F (y, f y - a)) hproj hprojlevel
    apply h.congr
    intro y
    apply Subtype.ext
    exact hback y
  have hinv₂ : ContMDiff 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ) ∞
      (fun y : U => ((e'.symm y).2 : symmetricOpenInterval r)) := by
    apply (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval r) _).mp
    exact (contMDiff_const.sub (hf.contMDiff.comp contMDiff_subtype_val)).congr
      (fun y => htime y)
  let c : SmoothTwoSidedCollar 𝓘(ℝ, MorseModel m) 𝓘(ℝ, MorseModel (m + 1))
      (Subtype.val : LevelSetSpace f a → MorseModel (m + 1)) :=
    { radius := r
      radius_pos := hrpos
      neighborhood := U
      toDiffeomorph :=
        { toEquiv := e'.toEquiv
          contMDiff_toFun := he
          contMDiff_invFun := hinv₁.prodMk hinv₂ }
      zero_eq := hzero }
  exact ⟨c, hvalue⟩

end Poincare.Manifold.RegularLevel
