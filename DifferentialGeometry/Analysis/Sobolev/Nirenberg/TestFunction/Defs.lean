import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

noncomputable def nirenbergTestFunction
    (k : Fin d) (h : ℝ) (η u : E → ℝ) : E → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.diffQuot k (-h)
    (fun y : E => η y ^ 2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y)

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
