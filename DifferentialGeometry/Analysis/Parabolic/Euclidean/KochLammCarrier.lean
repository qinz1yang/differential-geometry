import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammGerms
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The completed compatible Koch--Lamm path carrier

The ambient type `KLPathData` is complete, but its two gradient-germ arms are
initially independent.  This file cuts out the exact completed path space as
the closure of smooth data for which those germs are the genuine spatial
Frechet derivative of the value field.

This closure presentation is deliberately prior to the heat estimates.  A
nonlinear expression can first be defined on the smooth core and extended by
its Koch--Lamm Lipschitz estimate.  Likewise, the heat potential must prove its
own bound and distributional realization before it is extended; neither fact
is hidden in the carrier.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The spatial Frechet derivative of a space-time field, with time held
fixed. -/
def klSpaceDeriv (u : ℝ × V → F) (z : ℝ × V) : V →L[ℝ] F :=
  fderiv ℝ (fun y ↦ u (z.1, y)) z.2

/-- Smooth compatible data whose exact Koch--Lamm norm data belongs to the
dense core of the completed path space.  The bounded continuous value field
is stored on the closed slab; `value_eq` identifies it with the smooth
space-time representative there. -/
structure KLSmoothPath (T : ℝ) where
  A₀ : ℝ≥0
  A₂ : ℝ≥0
  Aₚ : ℝ≥0
  value : (Set.Icc (0 : ℝ) T × V) →ᵇ F
  field : ℝ × V → F
  smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) field
  value_eq : ∀ z : Set.Icc (0 : ℝ) T × V,
    value z = field (z.1.1, z.2)
  bounds : KLPath T A₀ A₂ Aₚ field (klSpaceDeriv field)

variable [Fact (1 ≤ klP V)]

/-- Exact ambient norm data represented by a smooth compatible path. -/
def KLSmoothPath.toData {T : ℝ} (u : KLSmoothPath (V := V) (F := F) T) :
    KLPathData (V := V) (F := F) (G := V →L[ℝ] F) T :=
  ⟨u.value, pathGradData u.bounds⟩

/-- The smooth compatible core inside the complete ambient norm-data space. -/
def KLPathCore (T : ℝ) :
    Set (KLPathData (V := V) (F := F) (G := V →L[ℝ] F) T) :=
  Set.range KLSmoothPath.toData

/-- The complete compatible Koch--Lamm path carrier. -/
abbrev KLPathSpace (T : ℝ) :=
  {u : KLPathData (V := V) (F := F) (G := V →L[ℝ] F) T //
    u ∈ closure (KLPathCore (V := V) (F := F) T)}

instance klPathSpace_complete (T : ℝ) :
    CompleteSpace (KLPathSpace (V := V) (F := F) T) :=
  isClosed_closure.completeSpace_coe

/-- Inclusion of exact smooth data into the completed carrier. -/
def KLPathCore.toSpace {T : ℝ} :
    KLPathCore (V := V) (F := F) T → KLPathSpace (V := V) (F := F) T :=
  Set.inclusion subset_closure

/-- The exact smooth core is dense in the completed compatible carrier. -/
theorem klPathCore_dense (T : ℝ) :
    DenseRange (KLPathCore.toSpace (V := V) (F := F) (T := T)) := by
  unfold KLPathCore.toSpace
  rw [denseRange_inclusion_iff]

/-- A smooth compatible path determines a point of the completed carrier. -/
def KLSmoothPath.toSpace {T : ℝ} (u : KLSmoothPath (V := V) (F := F) T) :
    KLPathSpace (V := V) (F := F) T :=
  ⟨u.toData, subset_closure ⟨u, rfl⟩⟩

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
