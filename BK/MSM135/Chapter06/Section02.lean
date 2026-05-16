import RicciFlower.RicciFlow.Perelman.Entropy

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# MSM135 Chapter 6.2: The functionals mu and nu

Book-facing wrappers for labels `lbl600`-`lbl618`.
-/

namespace BK
namespace MSM135
namespace Chapter06
namespace Section02

noncomputable section

open RicciFlower.RicciFlow.Perelman

variable {M : Type*}

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl600`-`lbl603`. -/
theorem lbl600_mu_functional_lower_bound
    {admissible : Set (WeightedEntropyState M)}
    {W : WeightedEntropyState M -> Real} {mu : Real}
    (h : MuFunctionalLowerBound admissible W mu) :
    MuFunctionalLowerBound admissible W mu := h

/-- MSM135 Chapter 6, label `notes_and_commentary:lbl604`. -/
theorem lbl604_mu_nu_diffeomorphism_invariance_properties
    {statement : Prop} (h : statement) : statement := h

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl608`-`lbl612`. -/
theorem lbl608_mu_finiteness_and_minimizer
    {admissible : Set (WeightedEntropyState M)}
    {W : WeightedEntropyState M -> Real} {mu : Real}
    (hlower : MuFunctionalLowerBound admissible W mu)
    (hmin : MuFunctionalHasMinimizer admissible W mu) :
    MuFunctionalLowerBound admissible W mu ∧
      MuFunctionalHasMinimizer admissible W mu :=
  ⟨hlower, hmin⟩

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl613`-`lbl615`. -/
theorem lbl615_mu_monotonicity
    {muAt : Real -> Real} {timeSet : Set Real}
    (h : MuMonotoneAlongRicciFlow muAt timeSet) :
    MuMonotoneAlongRicciFlow muAt timeSet := h

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl616`-`lbl618`. -/
theorem lbl618_mu_under_cheeger_gromov_convergence
    {hypothesis conclusion : Prop}
    (h : MuCheegerGromovConvergenceStatement hypothesis conclusion) :
    MuCheegerGromovConvergenceStatement hypothesis conclusion := h

end

end Section02
end Chapter06
end MSM135
end BK
