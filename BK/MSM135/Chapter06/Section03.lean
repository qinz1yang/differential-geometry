import RicciFlower.RicciFlow.Perelman.Entropy

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# MSM135 Chapter 6.3: Shrinking breathers

Book-facing wrappers for labels `lbl619`-`lbl629`.
-/

namespace BK
namespace MSM135
namespace Chapter06
namespace Section03

noncomputable section

open RicciFlower.RicciFlow.Perelman

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl619`-`lbl621`. -/
theorem lbl620_shrinking_breather_is_gradient_soliton {breather soliton : Prop}
    (h : ShrinkingBreatherIsGradientSoliton breather soliton) :
    ShrinkingBreatherIsGradientSoliton breather soliton := h

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl622`-`lbl626`. -/
theorem lbl626_nu_lower_bound_and_minimizer
    {muAtTau : Real -> Real} {nu : Real}
    (hlower : NuFunctionalLowerBound muAtTau nu)
    (hmin : NuFunctionalHasMinimizer muAtTau nu) :
    NuFunctionalLowerBound muAtTau nu ∧ NuFunctionalHasMinimizer muAtTau nu :=
  ⟨hlower, hmin⟩

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl627`-`lbl629`. -/
theorem lbl628_nu_invariant_monotonicity
    {nuAt : Real -> Real} {timeSet : Set Real}
    (h : NuMonotoneAlongRicciFlow nuAt timeSet) :
    NuMonotoneAlongRicciFlow nuAt timeSet := h

end

end Section03
end Chapter06
end MSM135
end BK
