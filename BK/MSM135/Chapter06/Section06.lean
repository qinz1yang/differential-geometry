import RicciFlower.RicciFlow.Perelman.Noncollapsing

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# MSM135 Chapter 6.6: Improved no-local-collapsing and diameter control

Book-facing wrappers for labels `lbl677`-`lbl696`.
-/

namespace BK
namespace MSM135
namespace Chapter06
namespace Section06

noncomputable section

open RicciFlower.RicciFlow.Perelman

variable {M : Type*}

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl677`-`lbl682`. -/
theorem lbl682_no_local_collapsing_improved
    {n : Nat} {T rho : Real} {balls : Set (ScaleControlledBall M)}
    (h : ImprovedNoLocalCollapsingTheorem n T rho balls) :
    ImprovedNoLocalCollapsingTheorem n T rho balls := h

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl683`-`lbl686`. -/
theorem lbl684_topping_diameter_control
    {diameterBound curvatureScaleBound : Real}
    (h : ToppingDiameterControl diameterBound curvatureScaleBound) :
    ToppingDiameterControl diameterBound curvatureScaleBound := h

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl688`-`lbl692`. -/
theorem lbl690_cheng_eigenvalue_comparison
    {lowerBound eigenvalueEstimate : Real}
    (h : ChengEigenvalueComparison lowerBound eigenvalueEstimate) :
    ChengEigenvalueComparison lowerBound eigenvalueEstimate := h

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl693`-`lbl696`. -/
theorem lbl694_heat_equation_no_local_collapsing_variant
    {hypothesis conclusion : Prop}
    (h : HeatEquationNoLocalCollapsingVariant hypothesis conclusion) :
    HeatEquationNoLocalCollapsingVariant hypothesis conclusion := h

end

end Section06
end Chapter06
end MSM135
end BK
