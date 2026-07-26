import DifferentialGeometry.Analysis.ODE.PhaseFlowPerturbation

set_option autoImplicit false

/-!
# Small-acceleration limit for the phase endpoint error

The quantitative phase endpoint error tends to zero with the Lipschitz
coefficient of the acceleration.  This is the selection interface used before
applying a quantitative inverse theorem.
-/

noncomputable section

open Filter Set Topology
open scoped NNReal Topology

namespace DifferentialGeometry
namespace PhaseFlow

/-- The phase endpoint error vanishes at zero acceleration Lipschitz
coefficient. -/
@[simp] theorem phaseErr_zero : phaseErr 0 = 0 := by
  apply NNReal.eq
  simp [phaseErr]
  rfl

/-- The phase endpoint error depends continuously on the acceleration
Lipschitz coefficient. -/
theorem phaseErr_cont : Continuous phaseErr := by
  unfold phaseErr
  apply Continuous.subtype_mk
  fun_prop

/-- The phase endpoint error tends to zero with the acceleration Lipschitz
coefficient. -/
theorem phaseErr_tendsto : Tendsto phaseErr (nhds 0) (nhds 0) := by
  have h : Tendsto phaseErr (nhds (0 : NNReal)) (nhds (phaseErr 0)) :=
    phaseErr_cont.continuousAt
  simpa using h

/-- Every positive error threshold eventually contains the phase endpoint
error near zero acceleration Lipschitz coefficient. -/
theorem phaseErr_lt_ev {eps : NNReal} (heps : 0 < eps) :
    ∀ᶠ k in nhds 0, phaseErr k < eps :=
  phaseErr_tendsto (Iio_mem_nhds heps)

end PhaseFlow
end DifferentialGeometry
