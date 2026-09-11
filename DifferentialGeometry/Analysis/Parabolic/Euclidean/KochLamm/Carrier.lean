import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Germs
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

def kochLammSpaceDeriv (u : ℝ × V → F) (z : ℝ × V) : V →L[ℝ] F :=
  fderiv ℝ (fun y ↦ u (z.1, y)) z.2

structure KochLammSmoothPath (T : ℝ) where
  A₀ : ℝ≥0
  A₂ : ℝ≥0
  Aₚ : ℝ≥0
  value : (Set.Icc (0 : ℝ) T × V) →ᵇ F
  field : ℝ × V → F
  smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) field
  value_eq : ∀ z : Set.Icc (0 : ℝ) T × V,
    value z = field (z.1.1, z.2)
  bounds : KochLammPath T A₀ A₂ Aₚ field (kochLammSpaceDeriv field)

variable [Fact (1 ≤ kochLammP V)]

def KochLammSmoothPath.toPathProduct {T : ℝ}
    (u : KochLammSmoothPath (V := V) (F := F) T) :
    KochLammPathProduct (V := V) (F := F) (G := V →L[ℝ] F) T :=
  ⟨u.value, kochLammPathGradientProduct u.bounds⟩

def kochLammSmoothPathRange (T : ℝ) :
    Set (KochLammPathProduct (V := V) (F := F) (G := V →L[ℝ] F) T) :=
  Set.range KochLammSmoothPath.toPathProduct

abbrev KochLammPathSpace (T : ℝ) :=
  {u : KochLammPathProduct (V := V) (F := F) (G := V →L[ℝ] F) T //
    u ∈ closure (kochLammSmoothPathRange (V := V) (F := F) T)}

instance kochLammPathSpace_complete (T : ℝ) :
    CompleteSpace (KochLammPathSpace (V := V) (F := F) T) :=
  isClosed_closure.completeSpace_coe

def kochLammSmoothPathRangeInclusion {T : ℝ} :
    kochLammSmoothPathRange (V := V) (F := F) T →
      KochLammPathSpace (V := V) (F := F) T :=
  Set.inclusion subset_closure

omit [CompleteSpace F] in
theorem kochLammSmoothPathRange_dense (T : ℝ) :
    DenseRange (kochLammSmoothPathRangeInclusion (V := V) (F := F) (T := T)) := by
  unfold kochLammSmoothPathRangeInclusion
  rw [denseRange_inclusion_iff]

def KochLammSmoothPath.toPathSpace {T : ℝ}
    (u : KochLammSmoothPath (V := V) (F := F) T) :
    KochLammPathSpace (V := V) (F := F) T :=
  ⟨u.toPathProduct, subset_closure ⟨u, rfl⟩⟩

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
