import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Spaces
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

structure KochLammCylinderIndex (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (T : ℝ) where
  center : V
  radius : ℝ
  radius_pos : 0 < radius
  time_le : radius ^ 2 ≤ T

def kochLammCylinderMeasure {T : ℝ} (i : KochLammCylinderIndex V T) : Measure (ℝ × V) :=
  (kochLammVolume : Measure (ℝ × V)).restrict (kochLammCylinder i.center i.radius)

def kochLammLateMeasure {T : ℝ} (i : KochLammCylinderIndex V T) : Measure (ℝ × V) :=
  (kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder i.center i.radius)

variable {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [Fact (1 ≤ kochLammP V)] [Fact (kochLammP V ≠ ∞)]
  [Fact (1 ≤ kochLammQ V)] [Fact (kochLammQ V ≠ ∞)]

abbrev KochLammL2Family (T : ℝ) (G : Type*)
    [NormedAddCommGroup G] :=
  lp (fun i : KochLammCylinderIndex V T ↦ Lp G 2 (kochLammCylinderMeasure i)) ∞

abbrev KochLammLpFamily (T : ℝ) (G : Type*)
    [NormedAddCommGroup G] :=
  lp (fun i : KochLammCylinderIndex V T ↦ Lp G (kochLammP V) (kochLammLateMeasure i)) ∞

abbrev KochLammL1Family (T : ℝ) (F : Type*)
    [NormedAddCommGroup F] :=
  lp (fun i : KochLammCylinderIndex V T ↦ Lp F 1 (kochLammCylinderMeasure i)) ∞

abbrev KochLammLqFamily (T : ℝ) (F : Type*)
    [NormedAddCommGroup F] :=
  lp (fun i : KochLammCylinderIndex V T ↦ Lp F (kochLammQ V) (kochLammLateMeasure i)) ∞

abbrev KochLammPathProduct (T : ℝ) :=
  ((Set.Icc (0 : ℝ) T × V) →ᵇ F) ×
    KochLammL2Family (V := V) T G × KochLammLpFamily (V := V) T G

abbrev KochLammSourceZeroProduct (T : ℝ) :=
  KochLammL1Family (V := V) T F × KochLammLqFamily (V := V) T F

abbrev KochLammSourceOneProduct (T : ℝ) :=
  KochLammL2Family (V := V) T F × KochLammLpFamily (V := V) T F

section Complete

omit [NormedSpace ℝ F] [NormedSpace ℝ G] [Fact (kochLammP V ≠ ∞)] [Fact (1 ≤ kochLammQ V)]
  [Fact (kochLammQ V ≠ ∞)] in
theorem kochLammPathProduct_complete (T : ℝ) :
    CompleteSpace (KochLammPathProduct (V := V) (F := F) (G := G) T) := by
  infer_instance

omit [NormedSpace ℝ F] [NormedSpace ℝ G] [Fact (1 ≤ kochLammP V)] [Fact (kochLammP V ≠ ∞)]
  [Fact (kochLammQ V ≠ ∞)] in
theorem kochLammSourceZeroProduct_complete (T : ℝ) :
    CompleteSpace (KochLammSourceZeroProduct (V := V) (F := F) T) := by
  infer_instance

omit [NormedSpace ℝ F] [Fact (kochLammP V ≠ ∞)] [Fact (1 ≤ kochLammQ V)] [Fact (kochLammQ V ≠ ∞)] in
theorem kochLammSourceOneProduct_complete (T : ℝ) :
    CompleteSpace (KochLammSourceOneProduct (V := V) (F := F) T) := by
  infer_instance

end Complete

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
