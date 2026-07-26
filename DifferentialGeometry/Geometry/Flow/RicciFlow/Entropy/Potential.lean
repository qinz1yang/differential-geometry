import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.Defs

set_option autoImplicit false

/-!
# Perelman potential reconstructed from a positive density

This file records the scalar inverse to Perelman's density parametrization and
the induced identity of weighted measures.  It contains no flow or regularity
assumptions.
-/

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open MeasureTheory

variable {M : Type*}

/-- The Perelman potential reconstructed from a density `u` at scale `tau`. -/
def perelmanPotential (n : Nat) (tau : Real) (u : M → Real) : M → Real :=
  fun x => -Real.log (u x / perelmanDensityPrefactor n tau)

/-- Perelman's scalar density prefactor is positive at every positive scale. -/
theorem prefactor_pos (n : Nat) {tau : Real} (htau : 0 < tau) :
    0 < perelmanDensityPrefactor n tau := by
  unfold perelmanDensityPrefactor
  exact Real.rpow_pos_of_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) htau) _

/-- Logarithmic normal form of Perelman's positive density prefactor. -/
theorem log_prefactor (n : Nat) {tau : Real} (htau : 0 < tau) :
    Real.log (perelmanDensityPrefactor n tau) =
      (-(n : Real) / 2) * Real.log (4 * Real.pi * tau) := by
  unfold perelmanDensityPrefactor
  change Real.log ((4 * Real.pi * tau) ^ (-(n : Real) / 2)) = _
  rw [Real.log_rpow (mul_pos (mul_pos (by norm_num) Real.pi_pos) htau)]

/-- Reconstructing the potential of a positive density recovers that density. -/
theorem density_potential (n : Nat) {tau : Real} (u : M → Real)
    (htau : 0 < tau) (hu : ∀ x, 0 < u x) :
    perelmanDensity n tau (perelmanPotential n tau u) = u := by
  funext x
  have hpref : 0 < perelmanDensityPrefactor n tau := prefactor_pos n htau
  have hratio : 0 < u x / perelmanDensityPrefactor n tau := div_pos (hu x) hpref
  simp only [perelmanDensity, perelmanPotential, neg_neg, Real.exp_log hratio]
  simpa only [mul_div_assoc] using mul_div_cancel_left₀ (u x) hpref.ne'

/-- The weighted measure of a reconstructed positive density is `u dμ`. -/
theorem weighted_potential [MeasurableSpace M] (mu : Measure M) (n : Nat)
    {tau : Real} (u : M → Real) (htau : 0 < tau) (hu : ∀ x, 0 < u x) :
    perelmanWeightedMeasure mu n tau (perelmanPotential n tau u) =
      mu.withDensity (ENNReal.ofReal ∘ u) := by
  unfold perelmanWeightedMeasure
  rw [density_potential n u htau hu]
  rfl

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
