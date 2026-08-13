import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammGerms
import Mathlib.Analysis.Calculus.ContDiff.Basic

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

def klSpaceDeriv (u : ℝ × V → F) (z : ℝ × V) : V →L[ℝ] F :=
  fderiv ℝ (fun y ↦ u (z.1, y)) z.2

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

def KLSmoothPath.toData {T : ℝ} (u : KLSmoothPath (V := V) (F := F) T) :
    KLPathData (V := V) (F := F) (G := V →L[ℝ] F) T :=
  ⟨u.value, pathGradData u.bounds⟩

def KLPathCore (T : ℝ) :
    Set (KLPathData (V := V) (F := F) (G := V →L[ℝ] F) T) :=
  Set.range KLSmoothPath.toData

abbrev KLPathSpace (T : ℝ) :=
  {u : KLPathData (V := V) (F := F) (G := V →L[ℝ] F) T //
    u ∈ closure (KLPathCore (V := V) (F := F) T)}

instance klPathSpace_complete (T : ℝ) :
    CompleteSpace (KLPathSpace (V := V) (F := F) T) :=
  isClosed_closure.completeSpace_coe

def KLPathCore.toSpace {T : ℝ} :
    KLPathCore (V := V) (F := F) T → KLPathSpace (V := V) (F := F) T :=
  Set.inclusion subset_closure

theorem klPathCore_dense (T : ℝ) :
    DenseRange (KLPathCore.toSpace (V := V) (F := F) (T := T)) := by
  unfold KLPathCore.toSpace
  rw [denseRange_inclusion_iff]

def KLSmoothPath.toSpace {T : ℝ} (u : KLSmoothPath (V := V) (F := F) T) :
    KLPathSpace (V := V) (F := F) T :=
  ⟨u.toData, subset_closure ⟨u, rfl⟩⟩

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
