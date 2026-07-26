import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-!
# The time-`L²` class of an interior-continuous, a.e.-bounded function

The continuous-embedding constructor `timeL2.ofContinuousOn` of `BochnerL2.lean`
requires continuity on the *closed* interval `[0,T]`.  Parabolic carriers built
from interior smoothing are typically continuous only on the *open* interior
`(0,T)` — they need not extend continuously to the endpoints — yet they are
controlled by an a.e. pointwise norm bound.  This file supplies the constructor
this situation needs:

  `ContinuousOn f (Set.Ioo 0 T)`  +  `∀ᵐ t, ‖f t‖ ≤ M`  ⟹  `f ∈ L²([0,T]; X)`.

The mechanism is standard finite-measure theory.  Because the two endpoints are
Lebesgue-null, `timeMeasure T = volume.restrict (Icc 0 T)` agrees with
`volume.restrict (Ioo 0 T)` (`MeasureTheory.Ioo_ae_eq_Icc`); continuity on the
measurable open interval therefore gives `AEStronglyMeasurable f (timeMeasure T)`
(`ContinuousOn.aestronglyMeasurable`).  Since `timeMeasure T` is finite, an
a.e.-bounded strongly-measurable function is `MemLp _ 2` (`MemLp.of_bound`).

## Main definitions

* `timeL2.ofContinuousOnIoo` — an interior-continuous, a.e.-bounded function
  regarded as an element of `timeL2 X T`.

## Main results

* `timeL2.memLp_of_continuousOn_Ioo` — the `MemLp _ 2` membership.
* `timeL2.coeFn_ofContinuousOnIoo` — `ofContinuousOnIoo … =ᵐ f`.
* `timeL2.exists_timeL2_of_continuousOn_Ioo` — the packaged existence form:
  there is a `timeL2 X T` element represented a.e. by `f`.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {T : ℝ} {f : ℝ → X}

omit [InnerProductSpace ℝ X] [CompleteSpace X] in
/-- A function continuous on the *open* interior `(0,T)` is strongly measurable
for the time measure: continuity on the measurable open interval gives strong
measurability against `volume.restrict (Ioo 0 T)`, which equals
`timeMeasure T = volume.restrict (Icc 0 T)` because the endpoints are null. -/
theorem aestronglyMeasurable_of_continuousOn_Ioo
    (hf : ContinuousOn f (Set.Ioo (0 : ℝ) T)) :
    AEStronglyMeasurable f (timeMeasure T) := by
  have hrestrict : timeMeasure T = volume.restrict (Set.Ioo (0 : ℝ) T) := by
    rw [timeMeasure, Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc).symm]
  rw [hrestrict]
  exact hf.aestronglyMeasurable measurableSet_Ioo

omit [InnerProductSpace ℝ X] [CompleteSpace X] in
/-- **Interior-continuous, a.e.-bounded `⟹` time-`L²`.**

A function continuous on the open interior `(0,T)` and a.e. bounded in norm by
`M` is square-Bochner-integrable for the time measure.  Unlike
`memLp_of_continuousOn`, this needs continuity only on `(0,T)`, not on the
closed interval `[0,T]`, so it applies to carriers built by interior smoothing
that need not extend continuously to the endpoints. -/
theorem memLp_of_continuousOn_Ioo
    (hf : ContinuousOn f (Set.Ioo (0 : ℝ) T)) {M : ℝ}
    (hM : ∀ᵐ t ∂(timeMeasure T), ‖f t‖ ≤ M) :
    MemLp f 2 (timeMeasure T) :=
  MemLp.of_bound (aestronglyMeasurable_of_continuousOn_Ioo hf) M hM

/-- A function continuous on the open interior `(0,T)` and a.e. norm-bounded,
regarded as an element of `L²([0,T]; X)`. -/
def ofContinuousOnIoo (hf : ContinuousOn f (Set.Ioo (0 : ℝ) T)) {M : ℝ}
    (hM : ∀ᵐ t ∂(timeMeasure T), ‖f t‖ ≤ M) : timeL2 X T :=
  (memLp_of_continuousOn_Ioo hf hM).toLp f

/-- The element `ofContinuousOnIoo hf hM` is represented a.e. by `f`. -/
theorem coeFn_ofContinuousOnIoo (hf : ContinuousOn f (Set.Ioo (0 : ℝ) T)) {M : ℝ}
    (hM : ∀ᵐ t ∂(timeMeasure T), ‖f t‖ ≤ M) :
    ofContinuousOnIoo hf hM =ᵐ[timeMeasure T] f :=
  (memLp_of_continuousOn_Ioo hf hM).coeFn_toLp

/-- **The packaged existence form.**  An interior-continuous, a.e.-bounded
function `f : ℝ → X` admits a genuine `L²([0,T]; X)` representative reproducing
it almost everywhere.  This is the shape consumed by the parabolic next-forcing
constructor: a carrier with interior continuity plus an a.e. mass bound yields
its time-`L²` class. -/
theorem exists_timeL2_of_continuousOn_Ioo
    (hf : ContinuousOn f (Set.Ioo (0 : ℝ) T)) {M : ℝ}
    (hM : ∀ᵐ t ∂(timeMeasure T), ‖f t‖ ≤ M) :
    ∃ F : timeL2 X T, (F : ℝ → X) =ᵐ[timeMeasure T] f :=
  ⟨ofContinuousOnIoo hf hM, coeFn_ofContinuousOnIoo hf hM⟩

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry
