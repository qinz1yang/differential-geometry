import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammSpaces
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Complete norm-data carriers for the Koch--Lamm spaces

The Koch--Lamm norms are suprema of local `L^p` norms over all admissible
parabolic cylinders.  Mathlib's dependent `lp` space at exponent `∞` is the
natural complete ambient space for exactly this data: one coordinate for each
cylinder, with the `lp ∞` norm taking the supremum.

The coordinates below are understood to be *scaled germs*.  For example, the
`L²` coordinate of a realized gradient is
`R^(-n/2)` times its restriction to the cylinder.  Thus the ambient norm is
the exact Koch--Lamm norm, not an unscaled surrogate.

This file proves completeness of the ambient norm data.  The next layer must
cut out the closed compatibility graph saying that all cylinder germs come
from one value field and one weak spatial derivative.  No heat mapping
property is assumed here.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace BoundedContinuousFunction

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- An exact admissible cylinder index for horizon `T`. -/
structure KLCylIndex (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (T : ℝ) where
  center : V
  radius : ℝ
  radius_pos : 0 < radius
  time_le : radius ^ 2 ≤ T

/-- The full cylinder measure belonging to an admissible index. -/
def klCylMeasure {T : ℝ} (i : KLCylIndex V T) : Measure (ℝ × V) :=
  (klVolume : Measure (ℝ × V)).restrict (klCyl i.center i.radius)

/-- The late half-cylinder measure belonging to an admissible index. -/
def klLateMeasure {T : ℝ} (i : KLCylIndex V T) : Measure (ℝ × V) :=
  (klVolume : Measure (ℝ × V)).restrict (klLateCyl i.center i.radius)

variable {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [Fact (1 ≤ klP V)] [Fact (klP V ≠ ∞)]
  [Fact (1 ≤ klQ V)] [Fact (klQ V ≠ ∞)]

/-- Bounded families of scaled full-cylinder `L²` germs. -/
abbrev KLL2Data (T : ℝ) (G : Type*)
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] :=
  lp (fun i : KLCylIndex V T ↦ Lp G 2 (klCylMeasure i)) ∞

/-- Bounded families of scaled late-cylinder `L^p` germs. -/
abbrev KLLpData (T : ℝ) (G : Type*)
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] :=
  lp (fun i : KLCylIndex V T ↦ Lp G (klP V) (klLateMeasure i)) ∞

/-- Bounded families of scaled full-cylinder `L¹` germs. -/
abbrev KLL1Data (T : ℝ) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :=
  lp (fun i : KLCylIndex V T ↦ Lp F 1 (klCylMeasure i)) ∞

/-- Bounded families of scaled late-cylinder `L^q` germs. -/
abbrev KLLqData (T : ℝ) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :=
  lp (fun i : KLCylIndex V T ↦ Lp F (klQ V) (klLateMeasure i)) ∞

/-- Complete ambient data for a Koch--Lamm path: a bounded continuous value
field on the closed slab, scaled local `L²` gradient germs, and scaled late
`L^(n+4)` gradient germs. -/
abbrev KLPathData (T : ℝ) :=
  ((Set.Icc (0 : ℝ) T × V) →ᵇ F) ×
    KLL2Data (V := V) T G × KLLpData (V := V) T G

/-- Complete ambient data for an ordinary `Y⁰` source. -/
abbrev KLSrc0Data (T : ℝ) :=
  KLL1Data (V := V) T F × KLLqData (V := V) T F

/-- Complete ambient data for a divergence `Y¹` source. -/
abbrev KLSrc1Data (T : ℝ) :=
  KLL2Data (V := V) T F × KLLpData (V := V) T F

section Complete

omit [NormedSpace ℝ F] [Fact (klP V ≠ ∞)] [Fact (1 ≤ klQ V)]
  [Fact (klQ V ≠ ∞)] in
/-- The exact path norm-data ambient is complete. -/
theorem klPathData_complete (T : ℝ) :
    CompleteSpace (KLPathData (V := V) (F := F) (G := G) T) := by
  infer_instance

omit [Fact (1 ≤ klP V)] [Fact (klP V ≠ ∞)] [Fact (klQ V ≠ ∞)] in
/-- The exact ordinary-source norm-data ambient is complete. -/
theorem klSrc0Data_complete (T : ℝ) :
    CompleteSpace (KLSrc0Data (V := V) (F := F) T) := by
  infer_instance

omit [Fact (klP V ≠ ∞)] [Fact (1 ≤ klQ V)] [Fact (klQ V ≠ ∞)] in
/-- The exact flux norm-data ambient is complete. -/
theorem klSrc1Data_complete (T : ℝ) :
    CompleteSpace (KLSrc1Data (V := V) (F := F) T) := by
  infer_instance

end Complete

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
