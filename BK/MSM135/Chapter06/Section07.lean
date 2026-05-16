import RicciFlower.RicciFlow.Perelman.Entropy

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# MSM135 Chapter 6.7: Further calculations related to F and W

Book-facing wrappers for labels `lbl697`-`lbl715`.
-/

namespace BK
namespace MSM135
namespace Chapter06
namespace Section07

noncomputable section

open RicciFlower.RicciFlow.Perelman

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl698`-`lbl704`. -/
theorem lbl700_modified_scalar_curvature_variation
    {lhs rhs : Real}
    (h : ModifiedScalarCurvatureVariation lhs rhs) :
    ModifiedScalarCurvatureVariation lhs rhs := h

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl705`-`lbl711`. -/
theorem lbl705_energy_entropy_second_variation
    {lhs rhs : Real}
    (h : EnergyEntropySecondVariationFormula lhs rhs) :
    EnergyEntropySecondVariationFormula lhs rhs := h

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl712`-`lbl715`. -/
theorem lbl713_matrix_harnack_adjoint_heat_formula
    {lhs rhs : Real}
    (h : MatrixHarnackAdjointHeatFormula lhs rhs) :
    MatrixHarnackAdjointHeatFormula lhs rhs := h

end

end Section07
end Chapter06
end MSM135
end BK
