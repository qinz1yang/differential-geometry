import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammSpaces
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.ContinuousMap.Bounded.Normed

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

structure KLCylIndex (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (T : ℝ) where
  center : V
  radius : ℝ
  radius_pos : 0 < radius
  time_le : radius ^ 2 ≤ T

def klCylMeasure {T : ℝ} (i : KLCylIndex V T) : Measure (ℝ × V) :=
  (klVolume : Measure (ℝ × V)).restrict (klCyl i.center i.radius)

def klLateMeasure {T : ℝ} (i : KLCylIndex V T) : Measure (ℝ × V) :=
  (klVolume : Measure (ℝ × V)).restrict (klLateCyl i.center i.radius)

variable {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [Fact (1 ≤ klP V)] [Fact (klP V ≠ ∞)]
  [Fact (1 ≤ klQ V)] [Fact (klQ V ≠ ∞)]

abbrev KLL2Data (T : ℝ) (G : Type*)
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] :=
  lp (fun i : KLCylIndex V T ↦ Lp G 2 (klCylMeasure i)) ∞

abbrev KLLpData (T : ℝ) (G : Type*)
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] :=
  lp (fun i : KLCylIndex V T ↦ Lp G (klP V) (klLateMeasure i)) ∞

abbrev KLL1Data (T : ℝ) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :=
  lp (fun i : KLCylIndex V T ↦ Lp F 1 (klCylMeasure i)) ∞

abbrev KLLqData (T : ℝ) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :=
  lp (fun i : KLCylIndex V T ↦ Lp F (klQ V) (klLateMeasure i)) ∞

abbrev KLPathData (T : ℝ) :=
  ((Set.Icc (0 : ℝ) T × V) →ᵇ F) ×
    KLL2Data (V := V) T G × KLLpData (V := V) T G

abbrev KLSrc0Data (T : ℝ) :=
  KLL1Data (V := V) T F × KLLqData (V := V) T F

abbrev KLSrc1Data (T : ℝ) :=
  KLL2Data (V := V) T F × KLLpData (V := V) T F

section Complete

omit [NormedSpace ℝ F] [Fact (klP V ≠ ∞)] [Fact (1 ≤ klQ V)]
  [Fact (klQ V ≠ ∞)] in
theorem klPathData_complete (T : ℝ) :
    CompleteSpace (KLPathData (V := V) (F := F) (G := G) T) := by
  infer_instance

omit [Fact (1 ≤ klP V)] [Fact (klP V ≠ ∞)] [Fact (klQ V ≠ ∞)] in
theorem klSrc0Data_complete (T : ℝ) :
    CompleteSpace (KLSrc0Data (V := V) (F := F) T) := by
  infer_instance

omit [Fact (klP V ≠ ∞)] [Fact (1 ≤ klQ V)] [Fact (klQ V ≠ ∞)] in
theorem klSrc1Data_complete (T : ℝ) :
    CompleteSpace (KLSrc1Data (V := V) (F := F) T) := by
  infer_instance

end Complete

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
