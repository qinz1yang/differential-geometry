import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.Defs

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

variable {M : Type*}

theorem potential_density (n : ℕ) {tau : ℝ} (htau : 0 < tau) (f : M → ℝ) :
    perelmanPotential n tau (perelmanDensity n tau f) = f := by
  funext x
  have hpref := (prefactor_pos n htau).ne'
  simp only [perelmanPotential, perelmanDensity]
  rw [mul_div_cancel_left₀ _ hpref, Real.log_exp, neg_neg]

theorem perelmanDensity_injective (n : ℕ) {tau : ℝ} (htau : 0 < tau) :
    Function.Injective (perelmanDensity (M := M) n tau) := by
  intro f g h
  have hh := congrArg (perelmanPotential n tau) h
  simpa only [potential_density n htau] using hh

end DifferentialGeometry.PDE.RicciFlow.Entropy
