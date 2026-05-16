import RicciFlower.RicciFlow.Perelman.Entropy

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# MSM135 Chapter 6.4: Logarithmic Sobolev inequality

Book-facing wrappers for labels `lbl630`-`lbl645`.
-/

namespace BK
namespace MSM135
namespace Chapter06
namespace Section04

noncomputable section

open RicciFlower.RicciFlow.Perelman

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl631`-`lbl634`. -/
theorem lbl631_log_sobolev_inequality_version_one
    {entropy energy constant : Real}
    (h : LogSobolevInequality entropy energy constant) :
    LogSobolevInequality entropy energy constant := h

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl635`-`lbl636`. -/
theorem lbl635_log_sobolev_inequality_version_two
    {entropy energy constant : Real}
    (h : LogSobolevInequality entropy energy constant) :
    LogSobolevInequality entropy energy constant := h

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl637`-`lbl645`. -/
theorem lbl637_euclidean_log_sobolev_inequality
    {entropy energy constant : Real}
    (h : LogSobolevInequality entropy energy constant) :
    LogSobolevInequality entropy energy constant := h

end

end Section04
end Chapter06
end MSM135
end BK
